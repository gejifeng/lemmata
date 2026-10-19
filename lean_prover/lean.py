from __future__ import annotations

import hashlib
import json
import os
import subprocess
import tempfile
import threading
from dataclasses import dataclass, field
from pathlib import Path

from .paths import ROOT, WORK_DIR as WORK
ELAN_BIN = Path.home() / ".elan" / "bin"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

_compile_sem = threading.Semaphore(int(os.environ.get("LEAN_PROVER_COMPILE_JOBS", "10")))
_cache: dict[str, "CompileResult"] = {}
_cache_lock = threading.Lock()


@dataclass
class Message:
    line: int
    col: int
    end_line: int
    severity: str
    text: str


@dataclass
class CompileResult:
    ok: bool  # no errors
    messages: list[Message] = field(default_factory=list)
    timed_out: bool = False
    stderr: str = ""

    @property
    def errors(self) -> list[Message]:
        return [m for m in self.messages if m.severity == "error"]

    @property
    def has_sorry(self) -> bool:
        return any("declaration uses `sorry`" in m.text or "declaration uses 'sorry'" in m.text for m in self.messages)

    def axioms_of(self, name: str) -> set[str] | None:
        for m in self.messages:
            if m.text.startswith(f"'{name}' depends on axioms:"):
                inner = m.text.split("[", 1)[1].rsplit("]", 1)[0]
                return {a.strip() for a in inner.split(",") if a.strip()}
            if m.text.startswith(f"'{name}' does not depend on any axioms"):
                return set()
        return None


def compile_lean(code: str, timeout: float = 240.0) -> CompileResult:
    key = hashlib.sha256(code.encode()).hexdigest()
    with _cache_lock:
        if key in _cache:
            return _cache[key]
    WORK.mkdir(exist_ok=True)
    env = dict(os.environ)
    env["PATH"] = f"{ELAN_BIN}:{env.get('PATH', '')}"
    with _compile_sem:
        fd, path = tempfile.mkstemp(suffix=".lean", dir=WORK)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as fh:
                fh.write(code)
            try:
                proc = subprocess.run(
                    ["lake", "env", "lean", "--json", path],
                    cwd=ROOT,
                    env=env,
                    capture_output=True,
                    text=True,
                    timeout=timeout,
                )
            except subprocess.TimeoutExpired:
                res = CompileResult(False, [Message(0, 0, 0, "error", f"Lean compilation timed out after {timeout:.0f}s (proof too slow: avoid heavy simp/nlinarith/decide searches)")], timed_out=True)
                return res
        finally:
            try:
                os.unlink(path)
            except OSError:
                pass
    messages: list[Message] = []
    for raw in proc.stdout.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            d = json.loads(raw)
        except json.JSONDecodeError:
            continue
        messages.append(
            Message(
                line=d.get("pos", {}).get("line", 0),
                col=d.get("pos", {}).get("column", 0),
                end_line=(d.get("endPos") or d.get("pos") or {}).get("line", 0),
                severity=d.get("severity", "error"),
                text=d.get("data", ""),
            )
        )
    ok = not any(m.severity == "error" for m in messages)
    if proc.returncode != 0 and ok:
        # e.g. crash without JSON message
        stderr = "\n".join(l for l in proc.stderr.splitlines() if "has local changes" not in l)
        if stderr.strip():
            messages.append(Message(0, 0, 0, "error", stderr.strip()[:2000]))
            ok = False
    res = CompileResult(ok, messages, stderr=proc.stderr[-2000:])
    with _cache_lock:
        _cache[key] = res
    return res
