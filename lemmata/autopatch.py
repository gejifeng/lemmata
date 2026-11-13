"""Deterministic repair: replace the proofs of failing `have ... := by ...` blocks with an automation combo."""
from __future__ import annotations

import re

from .lean import compile_lean

_ALTS = ["omega", "linarith", "positivity", "norm_num", "simp_all", "ring", "(field_simp; ring)",
         "nlinarith [sq_nonneg (0:ℤ)]", "grind", "aesop"]
# every alternative must close the goal: `first` stops at the first tactic that merely makes progress
COMBO = "first " + " ".join(f"| ({a}; done)" for a in _ALTS)
HAVE_RE = re.compile(r"^(\s*)(?:·\s*)?(?:have|show|suffices|obtain|calc)\b.*:=\s*by\b(.*)$")
TERM_HAVE_RE = re.compile(r"^(\s*)((?:·\s*)?(?:have|show)\b.+?):=(?!\s*by\b)(.*)$")


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _has_outer_colon(head: str) -> bool:
    """True when `have/show ...` carries an explicit `: Type` annotation at outer bracket depth 0."""
    stripped = head.lstrip().removeprefix("·").lstrip()
    if stripped.startswith("show"):
        return True
    s = re.sub(r"^\s*(?:·\s*)?have\b\s*", "", head)
    depth = 0
    for idx, ch in enumerate(s):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            return not (idx + 1 < len(s) and s[idx + 1] == "=")
    return False


def _have_header_prefix(line: str) -> str | None:
    """If `line` starts a patchable `have`/`show` block (`:= by` or typed `:= term`), return `... := by`."""
    if HAVE_RE.match(line):
        return line[: line.rfind(":= by")] + ":= by"
    if line.count(":=") == 1:
        m = TERM_HAVE_RE.match(line)
        if m and _has_outer_colon(m.group(2)):
            return (m.group(1) + m.group(2)).rstrip() + " := by"
    return None


def _block_for(lines: list[str], err_line: int, lo: int) -> tuple[int, int] | None:
    """Find the innermost patchable `have` line at or above err_line (index) whose block contains err_line.
    Returns (start index, end index exclusive) of the block including the header line."""
    for i in range(err_line, lo - 1, -1):
        if _have_header_prefix(lines[i]) is None:
            continue
        ind = _indent(lines[i])
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or _indent(lines[j]) > ind):
            j += 1
        while j > i + 1 and not lines[j - 1].strip():
            j -= 1
        if i <= err_line < j:
            return i, j
    return None


def _outer_blocks(lines: list[str], error_lines: list[int], start_line: int) -> list[tuple[int, int]]:
    lo = max(0, start_line - 1)
    blocks = set()
    for el in error_lines:
        idx = el - 1
        if idx < lo or idx >= len(lines):
            continue
        b = _block_for(lines, idx, lo)
        if b:
            blocks.add(b)
    return sorted(b for b in blocks if not any(o != b and o[0] <= b[0] and b[1] <= o[1] for o in blocks))


def autopatch(code: str, error_lines: list[int], start_line: int) -> str | None:
    """Return patched code (or None) — error_lines are 1-based line numbers in `code`;
    only lines >= start_line (1-based) may be modified."""
    lines = code.split("\n")
    outer = _outer_blocks(lines, error_lines, start_line)
    if not outer:
        return None
    for s, e in reversed(outer):
        header = lines[s]
        head = _have_header_prefix(header)
        if head is None:
            continue
        lines[s:e] = [head, " " * (_indent(header) + 2) + COMBO]
    return "\n".join(lines)


SEARCH_TAIL = " | exact?"  # exact? either closes the goal or fails
TRY_THIS = re.compile(r"Try this:\s*(?:\[apply\]\s*)?(.+)", re.S)


def try_autopatch(code: str, errors, start_line: int):
    """Replace failing `have` blocks with an automation combo that ends in `exact?` (library search).
    Where `exact?` fires, its suggestion is substituted, so the final proof never contains `exact?`.
    Blocks where automation fails are reverted so partial fixes on other `have` steps are preserved."""
    orig_lines = code.split("\n")
    outer = _outer_blocks(orig_lines, [m.line for m in errors], start_line)
    if not outer:
        return None
    combo_with_search = COMBO + SEARCH_TAIL
    patched_lines: list[str] = []
    cursor = 0
    block_records = []  # (s, e, head_line_1based, tac_line_1based, head_str, indent_str)
    for s, e in outer:
        patched_lines.extend(orig_lines[cursor:s])
        header = orig_lines[s]
        head = _have_header_prefix(header)
        assert head is not None
        ind_str = " " * (_indent(header) + 2)
        head_ln = len(patched_lines) + 1
        tac_ln = head_ln + 1
        patched_lines.append(head)
        patched_lines.append(ind_str + combo_with_search)
        block_records.append((s, e, head_ln, tac_ln, head, ind_str))
        cursor = e
    patched_lines.extend(orig_lines[cursor:])
    patched = "\n".join(patched_lines)
    if patched == code:
        return None
    res = compile_lean(patched, timeout=300)
    err_lines = {m.line for m in res.errors}
    info_map: dict[int, str] = {}
    for m in res.messages:
        if m.severity == "information":
            t = TRY_THIS.match(m.text.strip())
            if t:
                info_map[m.line] = t.group(1).strip().split("\n")[0]
    replacements: dict[tuple[int, int], list[str]] = {}
    for s, e, head_ln, tac_ln, head, ind_str in block_records:
        if head_ln in err_lines or tac_ln in err_lines:
            continue
        tac = info_map.get(tac_ln, COMBO)
        replacements[(s, e)] = [head, ind_str + tac]
    if not replacements:
        return None
    final_lines = list(orig_lines)
    for (s, e), new_blk in sorted(replacements.items(), reverse=True):
        final_lines[s:e] = new_blk
    final = "\n".join(final_lines)
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
