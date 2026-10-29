"""Suggest real Mathlib names for unknown identifiers in Lean errors."""
from __future__ import annotations

import difflib
import re
import threading
from collections import defaultdict

from .paths import NAMES_FILE
_lock = threading.Lock()
_loaded = False
_types: dict[str, str] = {}
_by_last: dict[str, list[str]] = defaultdict(list)
_tokens: dict[str, set[str]] = defaultdict(set)

UNKNOWN_PATTERNS = [
    re.compile(r"[Uu]nknown (?:identifier|constant) [`'«]?([^`'»\s]+)"),
    re.compile(r"the environment does not contain [`']([^`'\s]+)"),
    re.compile(r"invalid field [`']([^`'\s]+)[`']"),
]


def _load() -> None:
    global _loaded
    with _lock:
        if _loaded:
            return
        _loaded = True
        if not NAMES_FILE.exists():
            return
        with NAMES_FILE.open(encoding="utf-8", errors="replace") as fh:
            for line in fh:
                name, _, ty = line.rstrip("\n").partition("\t")
                if not name or "._" in name or name.startswith("_") or ".proof_" in name or ".match_" in name:
                    continue
                _types[name] = ty
                last = name.rsplit(".", 1)[-1]
                _by_last[last.lower()].append(name)
                for tok in re.split(r"[._]", last.lower()):
                    if len(tok) >= 3:
                        _tokens[tok].add(name)


def suggest(ident: str, k: int = 6) -> list[str]:
    _load()
    if not _types:
        return []
    ident = ident.strip("`'«»")
    if ident in _types:
        return [ident]
    last = ident.rsplit(".", 1)[-1]
    out: list[str] = []
    out.extend(sorted(_by_last.get(last.lower(), []), key=len)[:k])
    if len(out) < k:
        toks = [t for t in re.split(r"[._]", last.lower()) if len(t) >= 3]
        pool: dict[str, int] = defaultdict(int)
        for t in toks:
            for n in _tokens.get(t, ()):
                pool[n] += 1
        if toks:
            best = sorted(pool.items(), key=lambda kv: (-kv[1], len(kv[0])))[:4000]
            cands = [n for n, c in best if c >= max(1, len(toks) - 1)]
            scored = sorted(cands, key=lambda n: -difflib.SequenceMatcher(None, ident.lower(), n.lower()).ratio())
            for n in scored:
                if n not in out:
                    out.append(n)
                if len(out) >= k:
                    break
    return out[:k]


def annotate_errors(feedback: str) -> str:
    idents: list[str] = []
    for pat in UNKNOWN_PATTERNS:
        for m in pat.finditer(feedback):
            if m.group(1) not in idents:
                idents.append(m.group(1))
    if not idents:
        return ""
    lines = []
    for ident in idents[:5]:
        if "." not in ident and "_" not in ident:
            continue  # probably a local variable
        sug = suggest(ident)
        if not sug:
            continue
        if sug == [ident.strip("`'«»")]:
            lines.append(f"- `{ident}` exists (check namespace/arguments):")
        else:
            lines.append(f"- `{ident}` does not exist. Real Mathlib declarations with similar names:")
        for n in sug:
            ty = _types.get(n, "")
            lines.append(f"    {n} : {ty[:250]}")
    if not lines:
        return ""
    return "\n\nName hints (from the actual Mathlib environment):\n" + "\n".join(lines)
