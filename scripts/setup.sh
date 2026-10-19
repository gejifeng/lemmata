#!/usr/bin/env bash
# One-time setup: Lean toolchain, Mathlib (prebuilt cache), PutnamBench, and the Mathlib name index.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  echo "Installing elan (Lean toolchain manager)..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi

echo "Fetching Mathlib and its prebuilt cache (several GB)..."
lake exe cache get

PUTNAMBENCH_COMMIT=c8c8fa28aa1815a85991668ec0b020dd216d631d
if [ ! -d benchmarks/PutnamBench ]; then
  echo "Cloning PutnamBench..."
  mkdir -p benchmarks
  git clone https://github.com/trishullab/PutnamBench.git benchmarks/PutnamBench
  git -C benchmarks/PutnamBench checkout "$PUTNAMBENCH_COMMIT"
fi

if [ ! -s .work/mathlib_names.tsv ]; then
  echo "Building the Mathlib name index (10-20 minutes)..."
  lake env lean scripts/dump_mathlib_names.lean
fi

echo "Checking the environment..."
printf 'import Mathlib\nexample : (2 : ℕ) + 2 = 4 := by norm_num\n' > .work/smoke.lean
lake env lean .work/smoke.lean && echo "OK: Lean + Mathlib work."
