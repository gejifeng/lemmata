"""Minimal `.env` loader (standard library only).

Reads `KEY=VALUE` lines from the project's `.env` file (or the file named by `LEAN_PROVER_ENV_FILE`) into
`os.environ`. Variables that are already set in the environment are never overridden, so
`LEAN_PROVER_MODEL=x python -m ...` still wins over the file.
"""
from __future__ import annotations

import os
from pathlib import Path

DEFAULT_ENV_FILE = Path(__file__).resolve().parent.parent / ".env"


def parse(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export "):].lstrip()
        key, sep, value = line.partition("=")
        key = key.strip()
        if not sep or not key.replace("_", "").isalnum():
            continue
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in "\"'":
            value = value[1:-1]
        else:
            value = value.split(" #", 1)[0].rstrip()  # inline comment after an unquoted value
        values[key] = value
    return values


def load(path: str | os.PathLike | None = None) -> Path | None:
    """Load the env file into os.environ (without overriding). Returns the file used, or None."""
    env_path = Path(path or os.environ.get("LEAN_PROVER_ENV_FILE") or DEFAULT_ENV_FILE)
    try:
        text = env_path.read_text(encoding="utf-8")
    except OSError:
        return None
    for key, value in parse(text).items():
        os.environ.setdefault(key, value)
    return env_path
