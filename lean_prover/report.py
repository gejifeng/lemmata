"""Collect the final proofs from all runs, re-verify each one from scratch, and copy the verified ones to
results/proofs/.

    python -m lean_prover.report [main|easy|all]

A proof counts as verified only if it compiles, contains no `sorry`, depends only on the standard axioms
(propext, Classical.choice, Quot.sound), and states the theorem exactly as in PutnamBench.
"""
from __future__ import annotations

import re
import shutil
import sys
from pathlib import Path

from .benchmarks import SETS
from .lean import STANDARD_AXIOMS, compile_lean
from .paths import BENCH_DIR, RESULTS_DIR, ROOT, RUNS_DIR


def verify(name: str, code: str) -> bool:
    res = compile_lean(code + "\n")
    axioms = res.axioms_of(name)
    return (res.ok and not res.has_sorry and axioms is not None and axioms <= STANDARD_AXIOMS
            and statement_matches(name, code))


def statement_matches(name: str, code: str) -> bool:
    """The theorem statement must be identical (modulo whitespace) to the PutnamBench one."""
    src = (BENCH_DIR / f"{name}.lean").read_text(encoding="utf-8")

    def stmt(text: str) -> str:
        m = re.search(rf"theorem {re.escape(name)}\b(.*?):=", text, re.S)
        return re.sub(r"\s+", " ", m.group(1)).strip() if m else ""

    return bool(stmt(src)) and stmt(src) == stmt(code)


def main() -> None:
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    names = SETS[which]
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    candidates: dict[str, list[Path]] = {}
    for p in sorted(RUNS_DIR.glob("*/*/FINAL_proof.lean")):
        candidates.setdefault(p.parent.name, []).append(p)
    for p in sorted(RESULTS_DIR.glob("putnam_*.lean")):  # previously collected proofs
        candidates.setdefault(p.stem, []).append(p)
    n_ok = 0
    for name in names:
        status, src = "unsolved", ""
        for p in candidates.get(name, []):
            if verify(name, p.read_text(encoding="utf-8")):
                status, src = "VERIFIED", (str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p))
                if p.parent != RESULTS_DIR:
                    shutil.copy(p, RESULTS_DIR / f"{name}.lean")
                break
            status = "FAILED-RECHECK"
        n_ok += status == "VERIFIED"
        print(f"{name:18} {status:15} {src}")
    print(f"{n_ok}/{len(names)} verified")


if __name__ == "__main__":
    main()
