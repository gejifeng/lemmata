#!/usr/bin/env bash
# One-click setup on Linux/macOS (run ./install.sh): checks Python and Git, installs Lean (elan), Mathlib
# (prebuilt cache), PutnamBench and the Mathlib name index, asks for the API key, adds a launcher and opens the
# web UI. On Windows, double-click install.bat instead. Safe to run again: finished steps are skipped.
#   ./install.sh [--skip-name-index] [--skip-putnambench] [--no-shortcut] [--no-webui]
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
PUTNAMBENCH_COMMIT=c8c8fa28aa1815a85991668ec0b020dd216d631d

SKIP_NAME_INDEX=0 SKIP_PUTNAMBENCH=0 NO_SHORTCUT=0 NO_WEBUI=0
for arg in "$@"; do
  case "$arg" in
    --skip-name-index) SKIP_NAME_INDEX=1 ;;
    --skip-putnambench) SKIP_PUTNAMBENCH=1 ;;
    --no-shortcut) NO_SHORTCUT=1 ;;
    --no-webui) NO_WEBUI=1 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done

step() { printf '\n\033[36m==> %s\033[0m\n' "$1"; }
ok() { printf '    \033[32m%s\033[0m\n' "$1"; }
fail() { printf '\n\033[31mERROR: %s\033[0m\n' "$1" >&2; exit 1; }

# the command that installs packages on this system, for error messages (nothing is installed with sudo here)
install_hint() {
  if [ "$(uname)" = Darwin ]; then echo "brew install $*   (Homebrew: https://brew.sh)"
  elif command -v apt-get >/dev/null; then echo "sudo apt-get install -y $*"
  elif command -v dnf >/dev/null; then echo "sudo dnf install -y $*"
  elif command -v pacman >/dev/null; then echo "sudo pacman -S --needed $*"
  elif command -v zypper >/dev/null; then echo "sudo zypper install -y $*"
  else echo "install: $*"
  fi
}

# ---------------------------------------------------------------------------------------------------------------
step "Python 3.10 or newer, Git, curl"
PYTHON=""
for c in python3 python3.13 python3.12 python3.11 python3.10 python; do
  if command -v "$c" >/dev/null && "$c" -c 'import sys; sys.exit(sys.version_info < (3, 10))' 2>/dev/null; then
    PYTHON="$(command -v "$c")"; break
  fi
done
[ -n "$PYTHON" ] || fail "Python 3.10+ not found. Install it with:  $(install_hint python3)  and run ./install.sh again."
ok "using $PYTHON ($("$PYTHON" --version 2>&1))"
for tool in git curl; do
  command -v "$tool" >/dev/null || fail "$tool not found. Install it with:  $(install_hint "$tool")  and run ./install.sh again."
done
ok "$(git --version)"

# ---------------------------------------------------------------------------------------------------------------
step "Lean toolchain manager (elan)"
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v lake >/dev/null; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi
command -v lake >/dev/null || fail "elan installation failed."
ok "elan is in $HOME/.elan/bin"

# ---------------------------------------------------------------------------------------------------------------
step "Mathlib and its prebuilt cache (several GB, the first time takes a while)"
lake exe cache get
ok "Mathlib is ready"

# ---------------------------------------------------------------------------------------------------------------
if [ "$SKIP_PUTNAMBENCH" = 0 ]; then
  step "PutnamBench (only needed for benchmark runs)"
  if [ ! -d benchmarks/PutnamBench ]; then
    mkdir -p benchmarks
    git clone --quiet https://github.com/trishullab/PutnamBench.git benchmarks/PutnamBench
    git -C benchmarks/PutnamBench -c advice.detachedHead=false checkout --quiet "$PUTNAMBENCH_COMMIT"
  fi
  ok "benchmarks/PutnamBench"
fi

# ---------------------------------------------------------------------------------------------------------------
mkdir -p .work
if [ "$SKIP_NAME_INDEX" = 0 ]; then
  step "Mathlib name index (one time, 10-20 minutes)"
  [ -s .work/mathlib_names.tsv ] || lake env lean scripts/dump_mathlib_names.lean
  ok ".work/mathlib_names.tsv"
fi

# ---------------------------------------------------------------------------------------------------------------
step "Checking Lean + Mathlib"
printf 'import Mathlib\nexample : (2 : ℕ) + 2 = 4 := by norm_num\n' > .work/smoke.lean
lake env lean .work/smoke.lean
ok "Lean + Mathlib work"
printf '%s' "$PYTHON" > .work/python.txt

# ---------------------------------------------------------------------------------------------------------------
step "DeepSeek API key"
[ -f .env ] || cp .env.example .env
if [ "$("$PYTHON" -c 'from lemmata import llm; print(1 if llm.settings()["api_key"] else 0)')" = 1 ]; then
  ok "already set in .env"
elif [ -t 0 ]; then
  echo "    Get a key at https://platform.deepseek.com (API keys). Press Enter to skip and set it later in the web UI."
  read -rsp "    DeepSeek API key: " KEY; echo
  if [ -n "${KEY// /}" ]; then
    printf '%s\n' "$KEY" | "$PYTHON" -c 'import sys; from lemmata import dotenv; dotenv.update({"LEMMATA_API_KEY": sys.stdin.readline().strip()})'
    ok "saved to .env"
  else
    ok "skipped"
  fi
else
  ok "not asked (no terminal); set it in the web UI or in .env"
fi

# ---------------------------------------------------------------------------------------------------------------
if [ "$NO_SHORTCUT" = 0 ]; then
  step "Launcher"
  if [ "$(uname)" = Darwin ]; then
    launcher="$HOME/Desktop/Lemmata.command"
    printf '#!/bin/bash\nexec "%s/start_webui.sh"\n' "$ROOT" > "$launcher" && chmod +x "$launcher"
    ok "Lemmata.command on the desktop starts the web UI"
  else
    apps="${XDG_DATA_HOME:-$HOME/.local/share}/applications"
    mkdir -p "$apps"
    cat > "$apps/lemmata.desktop" <<EOF
[Desktop Entry]
Type=Application
Name=Lemmata
Comment=Natural language to Lean-checked proofs (web UI)
Exec="$ROOT/start_webui.sh"
Path=$ROOT
Terminal=true
Categories=Education;Science;Math;
EOF
    ok "Lemmata in the application menu starts the web UI"
  fi
fi

printf '\n\033[32mSetup finished.\033[0m Start the web UI any time with ./start_webui.sh (or the launcher).\n'
printf 'Command line: %s -m lemmata.campaign my_theorem.lean --hours 1\n' "$(basename "$PYTHON")"
if [ "$NO_WEBUI" = 0 ] && [ -t 0 ]; then
  exec ./start_webui.sh
fi
