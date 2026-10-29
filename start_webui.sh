#!/usr/bin/env bash
# Starts the lean_prover web UI (http://127.0.0.1:7860) and opens it in the browser.
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
exec python3 -m lean_prover.webui "$@"
