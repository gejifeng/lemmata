"""Local web UI: natural language -> Lean statement (confirmed by you) -> proof.

    python -m lemmata.webui              # opens http://127.0.0.1:7860
    python -m lemmata.webui --port 8000 --no-browser

Standard library only. Each proof runs as a `lemmata.campaign` subprocess with its output in
runs/web_<id>/, so a proof survives a page reload and can be stopped from the page. Closing the server stops
running proofs. The server listens on 127.0.0.1 only unless --host is given.
"""
from __future__ import annotations

import argparse
import atexit
import json
import os
import re
import secrets
import shutil
import signal
import subprocess
import sys
import threading
import time
import webbrowser
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from . import dotenv, llm
from .formalize import formalize
from .lean import ELAN_BIN
from .paths import NAMES_FILE, ROOT, RUNS_DIR
from .problem import check_statement, parse_lean_problem

WEB_DIR = Path(__file__).resolve().parent / "web"
JOB_ID = re.compile(r"^[0-9]{8}_[0-9]{6}_[0-9a-f]{4}$")
MAX_HOURS = 24.0

_procs: dict[str, subprocess.Popen] = {}
_tasks: dict[str, dict] = {}  # formalization requests
_lock = threading.Lock()


# --- environment and settings --------------------------------------------------------------------------------------

def environment() -> dict:
    lake = shutil.which("lake") or (ELAN_BIN / ("lake.exe" if os.name == "nt" else "lake")).exists()
    return {"lean": bool(lake), "mathlib": (ROOT / ".lake" / "packages" / "mathlib").is_dir(),
            "name_index": NAMES_FILE.exists()}


def public_settings() -> dict:
    s = llm.settings()
    key = s["api_key"]
    return {"base_url": s["base_url"], "model": s["model"], "style": s["style"], "has_key": bool(key),
            "key_hint": (key[:3] + "…" + key[-4:]) if len(key) > 10 else ("set" if key else ""),
            "models": llm.DEEPSEEK_MODELS, "styles": list(llm.API_STYLES)}


def save_settings(body: dict) -> dict:
    values = {}
    if (body.get("api_key") or "").strip():
        values["LEMMATA_API_KEY"] = body["api_key"].strip()
    for field, key in (("base_url", "LEMMATA_BASE_URL"), ("model", "LEMMATA_MODEL"),
                       ("style", "LEMMATA_API_STYLE")):
        v = (body.get(field) or "").strip()
        if v:
            if "\n" in v or "\r" in v:
                raise ValueError(f"invalid {field}")
            values[key] = v
    if values.get("LEMMATA_API_STYLE", "deepseek") not in llm.API_STYLES:
        raise ValueError("unknown API style")
    if values:
        dotenv.update(values)
    return public_settings()


# --- formalization tasks -------------------------------------------------------------------------------------------

def start_formalize(text: str, model: str | None) -> str:
    if not text.strip():
        raise ValueError("empty problem")
    tid = secrets.token_hex(6)
    task = {"state": "running", "log": [], "result": None, "error": ""}
    with _lock:
        _tasks[tid] = task

    def run() -> None:
        try:
            with llm.use_model(model):
                task["result"] = formalize(text, log=task["log"].append)
            task["state"] = "done"
        except Exception as exc:  # report every failure to the page
            task["error"] = str(exc)
            task["state"] = "error"
    threading.Thread(target=run, daemon=True).start()
    return tid


# --- proof jobs ----------------------------------------------------------------------------------------------------

def _job_dir(jid: str) -> Path:
    if not JOB_ID.match(jid):
        raise KeyError(jid)
    d = RUNS_DIR / f"web_{jid}"
    if not (d / "job.json").exists():
        raise KeyError(jid)
    return d


def start_job(lean: str, informal: str, model: str | None, hours: float) -> dict:
    problem = parse_lean_problem(lean, informal=informal)
    ok, errors = check_statement(problem)
    if not ok:
        raise ValueError("the statement does not compile:\n" + errors)
    hours = max(0.05, min(MAX_HOURS, float(hours)))
    jid = time.strftime("%Y%m%d_%H%M%S") + "_" + secrets.token_hex(2)
    d = RUNS_DIR / f"web_{jid}"
    d.mkdir(parents=True)
    (d / "problem.lean").write_text(problem.header + "\n\n" + problem.display() + "\n", encoding="utf-8")
    model = model or llm.settings()["model"]
    meta = {"id": jid, "name": problem.name, "model": model, "hours": hours, "informal": informal,
            "statement": problem.statement, "created": time.time()}
    (d / "job.json").write_text(json.dumps(meta, ensure_ascii=False, indent=2), encoding="utf-8")
    env = dict(os.environ, LEMMATA_MODEL=model, PYTHONUTF8="1", PYTHONIOENCODING="utf-8")
    cmd = [sys.executable, "-m", "lemmata.campaign", str(d / "problem.lean"), "--run", d.name,
           "--hours", f"{hours:g}"]
    kw: dict = {"creationflags": subprocess.CREATE_NO_WINDOW} if os.name == "nt" else {"start_new_session": True}
    with (d / "stdout.log").open("w", encoding="utf-8") as fh:
        proc = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=fh, stderr=subprocess.STDOUT, **kw)
    with _lock:
        _procs[jid] = proc
    return job_status(jid)


def _kill(proc: subprocess.Popen) -> None:
    if proc.poll() is not None:
        return
    if os.name == "nt":  # the campaign's Lean subprocesses must go too
        subprocess.run(["taskkill", "/PID", str(proc.pid), "/T", "/F"], capture_output=True)
    else:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except (ProcessLookupError, PermissionError):
            pass


def stop_job(jid: str) -> dict:
    d = _job_dir(jid)
    with _lock:
        proc = _procs.get(jid)
    if proc is None or proc.poll() is not None:
        return job_status(jid)
    _kill(proc)
    try:
        proc.wait(timeout=15)
    except subprocess.TimeoutExpired:
        pass
    meta = json.loads((d / "job.json").read_text(encoding="utf-8"))
    meta["stopped"] = True
    (d / "job.json").write_text(json.dumps(meta, ensure_ascii=False, indent=2), encoding="utf-8")
    return job_status(jid)


def _tail(path: Path, n: int) -> str:
    try:
        return "\n".join(path.read_text(encoding="utf-8", errors="replace").splitlines()[-n:])
    except OSError:
        return ""


def job_status(jid: str, *, full: bool = False) -> dict:
    d = _job_dir(jid)
    meta = json.loads((d / "job.json").read_text(encoding="utf-8"))
    with _lock:
        proc = _procs.get(jid)
    running = proc is not None and proc.poll() is None
    final = d / meta["name"] / "FINAL_proof.lean"
    stats = {}
    for f in ("summary.json", "progress.json"):
        try:
            stats = json.loads((d / f).read_text(encoding="utf-8"))
            break
        except (OSError, ValueError):
            continue
    if final.exists():
        state = "solved"
    elif running:
        state = "running"
    elif meta.get("stopped"):
        state = "stopped"
    elif (d / "summary.json").exists():
        state = "unsolved"
    elif proc is not None or re.search(r"(?m)^error:", _tail(d / "stdout.log", 20)):
        state = "error"  # the campaign exited without a result, e.g. the endpoint check failed
    else:
        state = "interrupted"  # the server was restarted while this job ran
    llm_stats = stats.get("llm") or {}
    out = {"id": jid, "name": meta["name"], "model": meta.get("model", ""), "hours": meta.get("hours"),
           "created": meta.get("created"), "state": state,
           "elapsed_s": stats.get("wall_s") or (time.time() - meta["created"] if running else None),
           "tokens": llm_stats.get("completion_tokens", 0), "calls": llm_stats.get("calls", 0)}
    if full:
        out["informal"] = meta.get("informal", "")
        out["problem"] = (d / "problem.lean").read_text(encoding="utf-8")
        out["log"] = _tail(d / "events.log", 300)
        if state in ("error", "interrupted"):
            out["log"] = (out["log"] + "\n" + _tail(d / "stdout.log", 40)).strip()
        out["proof"] = final.read_text(encoding="utf-8") if final.exists() else ""
    return out


def list_jobs() -> list[dict]:
    rows = []
    for d in sorted(RUNS_DIR.glob("web_*"), reverse=True):
        try:
            rows.append(job_status(d.name.removeprefix("web_")))
        except (KeyError, OSError, ValueError):
            continue
    return rows[:100]


@atexit.register
def _stop_all() -> None:
    for proc in list(_procs.values()):
        _kill(proc)


# --- HTTP ----------------------------------------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    server_version = "lemmata"
    allowed_hosts: set[str] = set()

    def log_message(self, fmt, *args):  # keep the console quiet
        pass

    def _send(self, status: int, body: bytes, ctype: str, extra: dict | None = None) -> None:
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _json(self, obj, status: int = 200) -> None:
        self._send(status, json.dumps(obj, ensure_ascii=False).encode("utf-8"), "application/json; charset=utf-8")

    def _host_ok(self) -> bool:
        # rejects DNS-rebinding requests whose Host is some other site's name
        return not self.allowed_hosts or (self.headers.get("Host") or "") in self.allowed_hosts

    def do_GET(self) -> None:
        if not self._host_ok():
            return self._send(403, b"forbidden host", "text/plain")
        path = self.path.split("?", 1)[0]
        try:
            if path in ("/", "/index.html"):
                return self._send(200, (WEB_DIR / "index.html").read_bytes(), "text/html; charset=utf-8")
            if path == "/api/status":
                return self._json({"env": environment(), "settings": public_settings()})
            if path == "/api/jobs":
                return self._json(list_jobs())
            m = re.fullmatch(r"/api/jobs/([\w]+)", path)
            if m:
                return self._json(job_status(m.group(1), full=True))
            m = re.fullmatch(r"/api/jobs/([\w]+)/proof\.lean", path)
            if m:
                st = job_status(m.group(1), full=True)
                return self._send(200, st["proof"].encode("utf-8"), "text/plain; charset=utf-8",
                                  {"Content-Disposition": f'attachment; filename="{st["name"]}.lean"'})
            m = re.fullmatch(r"/api/formalize/(\w+)", path)
            if m and m.group(1) in _tasks:
                return self._json(_tasks[m.group(1)])
        except KeyError:
            pass
        self._json({"error": "not found"}, 404)

    def do_POST(self) -> None:
        # a custom header cannot be sent cross-site without a CORS preflight, which this server never grants
        if not self._host_ok() or self.headers.get("X-Lemmata") != "1":
            return self._send(403, b"forbidden", "text/plain")
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(min(n, 1_000_000)) or b"{}")
        except ValueError:
            return self._json({"error": "invalid JSON"}, 400)
        path = self.path.split("?", 1)[0]
        try:
            if path == "/api/settings":
                return self._json(save_settings(body))
            if path == "/api/ping":
                with llm.use_model(body.get("model")):
                    try:
                        return self._json({"ok": True, "reply": llm.ping()})
                    except llm.LLMFailure as exc:
                        return self._json({"ok": False, "error": str(exc)})
            if path == "/api/formalize":
                return self._json({"id": start_formalize(body.get("text", ""), body.get("model"))})
            if path == "/api/check":
                try:
                    problem = parse_lean_problem(body.get("lean", ""))
                except ValueError as exc:
                    return self._json({"ok": False, "errors": str(exc)})
                ok, errors = check_statement(problem)
                return self._json({"ok": ok, "name": problem.name, "errors": errors})
            if path == "/api/prove":
                return self._json(start_job(body.get("lean", ""), body.get("informal", ""), body.get("model"),
                                            body.get("hours", 1)))
            m = re.fullmatch(r"/api/jobs/([\w]+)/stop", path)
            if m:
                return self._json(stop_job(m.group(1)))
        except KeyError:
            return self._json({"error": "not found"}, 404)
        except (ValueError, OSError, llm.LLMFailure) as exc:
            return self._json({"error": str(exc)}, 400)
        self._json({"error": "not found"}, 404)


def main() -> None:
    ap = argparse.ArgumentParser(description="Lemmata web UI")
    ap.add_argument("--host", default="127.0.0.1", help="address to listen on (default: this computer only)")
    ap.add_argument("--port", type=int, default=7860)
    ap.add_argument("--no-browser", action="store_true", help="do not open a browser window")
    args = ap.parse_args()
    RUNS_DIR.mkdir(parents=True, exist_ok=True)
    server = None
    for port in range(args.port, args.port + 20):
        try:
            server = ThreadingHTTPServer((args.host, port), Handler)
            break
        except OSError:
            continue
    if server is None:
        sys.exit(f"error: no free port in {args.port}-{args.port + 19}")
    port = server.server_address[1]
    if args.host in ("127.0.0.1", "localhost", "::1"):
        Handler.allowed_hosts = {f"127.0.0.1:{port}", f"localhost:{port}", f"[::1]:{port}"}
    else:
        print(f"warning: listening on {args.host}; anyone who can reach this address can use your API key",
              flush=True)
    url = f"http://127.0.0.1:{port}"
    env = environment()
    print(f"Lemmata web UI: {url}  (Ctrl+C to stop)", flush=True)
    if not (env["lean"] and env["mathlib"]):
        print("warning: Lean/Mathlib not found; run ./install.sh (Linux/macOS) or install.bat (Windows) first",
              flush=True)
    if not args.no_browser:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
