"""Index of earlier attempts, keyed by (context, statement), so a new run can continue from the best previous
candidate instead of starting from scratch."""
from __future__ import annotations

import hashlib
import json
import re
import threading
from pathlib import Path

from .problem import Problem, load_putnam

from .paths import RUNS_DIR as RUNS
_lock = threading.Lock()
_index: dict[str, list[dict]] | None = None


def key_of(problem: Problem) -> str:
    norm = lambda t: re.sub(r"\s+", " ", t or "").strip()
    return hashlib.sha256((norm(problem.context) + "\n#\n" + norm(problem.statement)).encode()).hexdigest()


def error_count(feedback: str) -> int:
    n = feedback.count("Error at line")
    m = re.search(r"\.\.\. and (\d+) more errors", feedback)
    return n + (int(m.group(1)) if m else 0)


def _problem_for(dir_: Path) -> Problem | None:
    pj = dir_ / "problem.json"
    if pj.exists():
        try:
            return Problem(**json.loads(pj.read_text(encoding="utf-8")))
        except Exception:
            return None
    if re.fullmatch(r"putnam_\w+", dir_.name):
        try:
            return load_putnam(dir_.name)
        except Exception:
            return None
    return None


def _build() -> dict[str, list[dict]]:
    idx: dict[str, list[dict]] = {}
    for f in RUNS.glob("*/**/attempts.jsonl"):
        prob = _problem_for(f.parent)
        if prob is None:
            continue
        k = key_of(prob)
        for line in f.read_text(encoding="utf-8").splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r.get("solved") or not r.get("code") or not r.get("feedback"):
                continue
            if "forbidden" in r.get("verdict_reason", "") or "no code" in r.get("verdict_reason", ""):
                continue
            idx.setdefault(k, []).append({"code": r["code"], "feedback": r["feedback"],
                                           "errors": error_count(r["feedback"]), "src": str(f)})
    return idx


def best_previous(problem: Problem) -> dict | None:
    global _index
    with _lock:
        if _index is None:
            _index = _build()
        rows = _index.get(key_of(problem)) or []
    if not rows:
        return None
    return min(rows, key=lambda r: (r["errors"], len(r["code"])))
