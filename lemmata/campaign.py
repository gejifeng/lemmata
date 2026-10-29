"""Run the prover on a set of problems in parallel: PutnamBench names or your own Lean files.

    python -m lemmata.campaign my_theorem.lean --hours 1
    python -m lemmata.campaign putnam_1977_a5 putnam_1988_b1 --hours 1
    python -m lemmata.campaign --set easy --hours 6 --run my_run

A Lean file states one goal, `theorem name ... := by sorry`, after `import Mathlib` and optional definitions.
"""
from __future__ import annotations

import argparse
import json
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

from . import llm
from .benchmarks import SETS
from .decompose import solve
from .paths import RUNS_DIR
from .problem import check, load_problem


def main() -> None:
    ap = argparse.ArgumentParser(description="Prove Lean theorems with a Lean-checked LLM agent.")
    ap.add_argument("problems", nargs="*",
                    help="Lean files (my_theorem.lean) or PutnamBench names (putnam_1977_a5); default: --set")
    ap.add_argument("--set", choices=sorted(SETS), default="main", help="problem set used when no names are given")
    ap.add_argument("--run", default=time.strftime("run_%Y%m%d_%H%M%S"), help="output directory name under runs/")
    ap.add_argument("--hours", type=float, default=6.0, help="wall-clock budget for the whole campaign")
    ap.add_argument("--chains", type=int, default=1, help="parallel direct-proof chains per (sub)problem")
    ap.add_argument("--rounds", type=int, default=6, help="thinking rounds per chain")
    ap.add_argument("--max-depth", type=int, default=3, help="maximum decomposition depth")
    ap.add_argument("--sketches", type=int, default=3, help="decomposition attempts per (sub)problem")
    ap.add_argument("--resume-from", default="",
                    help="comma-separated earlier runs whose valid top-level skeletons are reused")
    ap.add_argument("--skip-ping", action="store_true", help="do not test the model endpoint before starting")
    args = ap.parse_args()

    specs = args.problems or SETS[args.set]
    try:
        problems = [load_problem(s) for s in specs]
    except (OSError, ValueError) as exc:
        sys.exit(f"error: {exc}")
    s = llm.settings()
    print(f"model: {s['model']} at {s['base_url']} ({s['style']} API)", flush=True)
    if not args.skip_ping:
        try:
            llm.ping()
        except llm.LLMFailure as exc:
            sys.exit(f"error: the model endpoint does not work: {exc}\n"
                     "Check LEMMATA_API_KEY / LEMMATA_BASE_URL / LEMMATA_MODEL in .env.")
    names = [p.name for p in problems]
    if len(set(names)) < len(names):
        sys.exit("error: two problems have the same theorem name")
    out = RUNS_DIR / args.run
    out.mkdir(parents=True, exist_ok=True)
    deadline = time.time() + args.hours * 3600
    t0 = time.time()
    log_lock = threading.Lock()

    def log(msg: str) -> None:
        with log_lock:
            line = f"[{time.time() - t0:7.0f}s] {msg}"
            print(line, flush=True)
            with (out / "events.log").open("a", encoding="utf-8") as fh:
                fh.write(line + "\n")

    results: dict[str, bool] = {}

    def work(prob) -> None:
        name = prob.name
        seeds = []
        for run_name in [r for r in args.resume_from.split(",") if r]:
            for f in sorted((RUNS_DIR / run_name / name).glob("sketch_*/skeletons.jsonl")):
                for line in f.read_text(encoding="utf-8").splitlines():
                    row = json.loads(line)
                    if row.get("ok"):
                        seeds.append(row["content"])
        try:
            cand = solve(prob, out / name, 0, chains=args.chains, rounds=args.rounds, max_depth=args.max_depth,
                         sketches=args.sketches + len(seeds), deadline=deadline, log=log, seed_skeletons=seeds)
        except Exception as exc:  # keep the campaign alive
            log(f"{name}: crashed {exc!r}")
            cand = None
        ok = False
        if cand is not None:
            v = check(prob, cand)
            ok = v.solved
            if ok:
                (out / name / "FINAL_proof.lean").write_text(v.code, encoding="utf-8")
        results[name] = ok
        log(f"=== {name}: {'SOLVED' if ok else 'unsolved'}  llm={llm.STATS}")
        (out / "summary.json").write_text(json.dumps({"results": results, "llm": llm.STATS,
                                                      "wall_s": time.time() - t0}, indent=2), encoding="utf-8")

    finished = threading.Event()

    def report_progress() -> None:  # read by the web UI
        while not finished.wait(15):
            (out / "progress.json").write_text(json.dumps({"results": results, "llm": llm.STATS,
                                                           "wall_s": time.time() - t0}), encoding="utf-8")
    threading.Thread(target=report_progress, daemon=True).start()
    with ThreadPoolExecutor(max_workers=len(names)) as ex:
        list(ex.map(work, problems))
    finished.set()
    log(f"DONE {sum(results.values())}/{len(names)} solved")


if __name__ == "__main__":
    main()
