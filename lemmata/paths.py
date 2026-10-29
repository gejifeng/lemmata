"""All filesystem locations used by lemmata, overridable by environment variables."""
from __future__ import annotations

import os
from pathlib import Path

# Lake project root (contains lakefile.toml); `lake env lean` is run from here.
ROOT = Path(os.environ.get("LEMMATA_ROOT", Path(__file__).resolve().parent.parent))
# Scratch files, caches and the Mathlib name index.
WORK_DIR = Path(os.environ.get("LEMMATA_WORK_DIR", ROOT / ".work"))
# One sub-directory per campaign run.
RUNS_DIR = Path(os.environ.get("LEMMATA_RUNS_DIR", ROOT / "runs"))
# PutnamBench Lean 4 sources (one `putnam_*.lean` file per problem).
BENCH_DIR = Path(os.environ.get("PUTNAMBENCH_DIR", ROOT / "benchmarks" / "PutnamBench" / "lean4" / "src"))
# Runtime-tunable search settings; re-read on every use, so a running campaign can be adjusted.
CONFIG_FILE = Path(os.environ.get("LEMMATA_CONFIG", ROOT / "config" / "default.json"))
# Verified proofs collected by `python -m lemmata.report`.
RESULTS_DIR = Path(os.environ.get("LEMMATA_RESULTS_DIR", ROOT / "results" / "proofs"))

NAMES_FILE = WORK_DIR / "mathlib_names.tsv"
SEARCH_CACHE = WORK_DIR / "search_cache.jsonl"
LEMMA_CACHE = WORK_DIR / "lemma_cache.jsonl"
