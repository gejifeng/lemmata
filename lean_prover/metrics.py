"""Per-run metrics: solved problems, tokens per problem / per solve, and error-category shares.

    python -m lean_prover.metrics RUN [RUN ...]
"""
from __future__ import annotations

import collections
import json
import re
import sys
from pathlib import Path

from .paths import RUNS_DIR as RUNS
LIMITS = {20000, 14000, 10000, 6000}

CATS = [
    ("unknown_name", re.compile(r"Unknown (identifier|constant)|does not contain|invalid field")),
    ("syntax", re.compile(r"unexpected token|expected '|unknown tactic|invalid 'import'")),
    ("type_mismatch", re.compile(r"[Tt]ype mismatch|Application type mismatch|failed to synthesize")),
    ("rewrite_failed", re.compile(r"rewrite. failed|motive is not type correct|did not find an occurrence")),
    ("tactic_failed", re.compile(r"linarith failed|omega could not|nlinarith|positivity failed|simp. made no progress|failed with a nested error|decide failed")),
    ("unsolved_goals", re.compile(r"unsolved goals")),
    ("timeout", re.compile(r"timed out|maximum recursion|heartbeats")),
]


def classify(feedback: str) -> set[str]:
    cats = set()
    for name, rx in CATS:
        if rx.search(feedback):
            cats.add(name)
    return cats or ({"other"} if feedback else set())


def problem_tokens(pdir: Path) -> int:
    tot = 0
    for f in pdir.rglob("attempts.jsonl"):
        for l in f.read_text(encoding="utf-8").splitlines():
            tot += json.loads(l).get("response_tokens") or 0
    for f in pdir.rglob("skeletons.jsonl"):
        for l in f.read_text(encoding="utf-8").splitlines():
            tot += json.loads(l).get("tokens") or 0
    for f in pdir.rglob("plan_tokens.json"):
        tot += json.loads(f.read_text()).get("tokens") or 0
    return tot


def report(run: str) -> None:
    rd = RUNS / run
    probs = sorted(p for p in rd.iterdir() if p.is_dir() and p.name.startswith("putnam_"))
    print(f"== {run}")
    solved = 0
    total_tokens = 0
    cat = collections.Counter()
    n_failed = 0
    trunc = 0
    n_attempts = 0
    for p in probs:
        ok = (p / "FINAL_proof.lean").exists()
        solved += ok
        tok = problem_tokens(p)
        total_tokens += tok
        print(f"   {p.name:16} {'SOLVED' if ok else '      '} tokens={tok}")
        for f in p.rglob("attempts.jsonl"):
            for l in f.read_text(encoding="utf-8").splitlines():
                r = json.loads(l)
                n_attempts += 1
                trunc += (r.get("response_tokens") in LIMITS)
                if not r.get("solved") and r.get("feedback"):
                    n_failed += 1
                    cat.update(classify(r["feedback"]))
    print(f"   solved {solved}/{len(probs)}; tokens total {total_tokens}; "
          f"tokens per solved problem {total_tokens // max(1, solved)}")
    print(f"   attempts {n_attempts}; hit token limit {trunc}; failed-with-feedback {n_failed}")
    print("   error categories (share of failed attempts): " +
          ", ".join(f"{k} {v / max(1, n_failed):.0%}" for k, v in cat.most_common()))


if __name__ == "__main__":
    for r in sys.argv[1:]:
        report(r)
