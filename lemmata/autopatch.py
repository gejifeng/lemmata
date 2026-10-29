"""Deterministic repair: replace the proofs of failing `have ... := by ...` blocks with an automation combo."""
from __future__ import annotations

import re

from .lean import compile_lean

_ALTS = ["omega", "linarith", "positivity", "norm_num", "simp_all", "ring", "(field_simp; ring)",
         "nlinarith [sq_nonneg (0:ℤ)]", "grind", "aesop"]
# every alternative must close the goal: `first` stops at the first tactic that merely makes progress
COMBO = "first " + " ".join(f"| ({a}; done)" for a in _ALTS)
HAVE_RE = re.compile(r"^(\s*)(?:·\s*)?(?:have|show|suffices|obtain|calc)\b.*:=\s*by\b(.*)$")


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _block_for(lines: list[str], err_line: int, lo: int) -> tuple[int, int] | None:
    """Find the innermost `... := by` line at or above err_line (index) whose block contains err_line.
    Returns (start index, end index exclusive) of the block including the header line."""
    for i in range(err_line, lo - 1, -1):
        m = HAVE_RE.match(lines[i])
        if not m:
            continue
        ind = _indent(lines[i])
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or _indent(lines[j]) > ind):
            j += 1
        if i <= err_line < j:
            return i, j
    return None


def autopatch(code: str, error_lines: list[int], start_line: int) -> str | None:
    """Return patched code (or None) — error_lines are 1-based line numbers in `code`;
    only lines >= start_line (1-based) may be modified."""
    lines = code.split("\n")
    lo = max(0, start_line - 1)
    blocks = set()
    for el in error_lines:
        idx = el - 1
        if idx < lo or idx >= len(lines):
            continue
        b = _block_for(lines, idx, lo)
        if b:
            blocks.add(b)
    if not blocks:
        return None
    # keep only outermost blocks
    outer = [b for b in blocks if not any(o != b and o[0] <= b[0] and b[1] <= o[1] for o in blocks)]
    for s, e in sorted(outer, reverse=True):
        header = lines[s]
        m = HAVE_RE.match(header)
        head = header[: header.rfind(":= by")] + ":= by"
        new = [head, " " * (_indent(header) + 2) + COMBO]
        lines[s:e] = new
    return "\n".join(lines)


SEARCH_TAIL = " | exact?"  # exact? either closes the goal or fails
TRY_THIS = re.compile(r"Try this:\s*(?:\[apply\]\s*)?(.+)", re.S)


def try_autopatch(code: str, errors, start_line: int):
    """Replace failing `have` blocks with an automation combo that ends in `exact?` (library search).
    Where `exact?` fires, its suggestion is substituted, so the final proof never contains `exact?`."""
    global COMBO
    base = COMBO
    COMBO = base + SEARCH_TAIL
    try:
        patched = autopatch(code, [m.line for m in errors], start_line)
    finally:
        COMBO = base
    if patched is None or patched == code:
        return None
    res = compile_lean(patched, timeout=300)
    lines = patched.split("\n")
    for m in res.messages:
        if m.severity != "information":
            continue
        t = TRY_THIS.match(m.text.strip())
        if t and 0 < m.line <= len(lines) and SEARCH_TAIL.strip() in lines[m.line - 1]:
            indent = lines[m.line - 1][: len(lines[m.line - 1]) - len(lines[m.line - 1].lstrip())]
            lines[m.line - 1] = indent + t.group(1).strip().split("\n")[0]
    final = "\n".join(l.replace(SEARCH_TAIL, "") for l in lines)
    if final == code:
        return None
    return final, compile_lean(final)


def remove_dead_tactics(code: str, errors, start_line: int, rounds: int = 3):
    """Delete tactics that Lean reports as running with no goals left ("No goals to be solved").
    Returns (new_code, CompileResult) or None if nothing was removed."""
    changed = False
    res = None
    for _ in range(rounds):
        lines = code.split("\n")
        dead = sorted({m.line - 1 for m in errors if "No goals to be solved" in m.text
                       and start_line - 1 <= m.line - 1 < len(lines)}, reverse=True)
        if not dead:
            break
        for i in dead:
            ind = _indent(lines[i])
            j = i + 1
            while j < len(lines) and lines[j].strip() and _indent(lines[j]) > ind:
                j += 1
            stripped = lines[i].lstrip()
            if stripped.startswith("·"):
                break  # a focused bullet: removing it could change structure; leave it
            del lines[i:j]
            changed = True
        code = "\n".join(lines)
        res = compile_lean(code)
        errors = res.errors
        if res.ok:
            break
    if not changed:
        return None
    return code, res
