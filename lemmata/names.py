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
    re.compile(r"[Uu]nknown (?:identifier|constant) [`'«]?([^`'»\s:]+)"),
    re.compile(r"[Tt]he environment does not contain [`'«]?([^`'»\s:]+)"),
    re.compile(r"[Ii]nvalid field [`'«]?([^`'»\s:]+)[`'»]?"),
]

_CAMEL_RE = re.compile(r"([a-z0-9])([A-Z])")
_STOP_TOKENS = {"the", "and", "for", "with"}


def _tokenize(s: str) -> list[str]:
    s = _CAMEL_RE.sub(r"\1_\2", s).lower()
    return [t for t in re.split(r"[._]+", s) if len(t) >= 3 and t not in _STOP_TOKENS]


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
                for tok in set(_tokenize(name)):
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
        toks = list(dict.fromkeys(_tokenize(ident)))
        pool: dict[str, int] = defaultdict(int)
        for t in toks:
            for n in _tokens.get(t, ()):
                pool[n] += 1
        if toks:
            best = sorted(pool.items(), key=lambda kv: (-kv[1], len(kv[0])))[:4000]
            top_hits = best[0][1] if best else 0
            min_hits = max(2, top_hits - 1) if top_hits >= 2 else 1
            cands = [n for n, c in best if c >= min_hits]
            scored = sorted(cands, key=lambda n: (-pool[n], -difflib.SequenceMatcher(None, ident.lower(), n.lower()).ratio(), len(n)))
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
    has_missing = False
    for ident in idents[:5]:
        if "." not in ident and "_" not in ident and not _CAMEL_RE.search(ident):
            continue  # probably a local variable
        sug = suggest(ident)
        if not sug:
            lines.append(f"- `{ident}` does not exist in this Mathlib.")
            has_missing = True
            continue
        if sug == [ident.strip("`'«»")]:
            lines.append(f"- `{ident}` exists (check namespace/arguments):")
        else:
            has_missing = True
            lines.append(f"- `{ident}` does not exist. Real Mathlib declarations with similar names:")
        for n in sug:
            ty = _types.get(n, "")
            lines.append(f"    {n} : {ty[:250]}")
    if not lines:
        return ""
    if has_missing:
        lines.append("  Note: never keep a non-existent identifier. If none of the real declarations above is a "
                     "direct match (or its type uses subtypes/bundled equivalences differently), replace it with an "
                     "explicit `have h : ... := by ...` step proved from definitions and basic tactics.")
    return "\n\nName hints (from the actual Mathlib environment):\n" + "\n".join(lines)
