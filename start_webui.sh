#!/usr/bin/env bash
# Starts the Lemmata web UI (http://127.0.0.1:7860) and opens it in the browser.
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
PYTHON=python3
[ -s .work/python.txt ] && PYTHON="$(cat .work/python.txt)"
exec "$PYTHON" -m lemmata.webui "$@"
