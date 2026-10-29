"""Turn an attempt that compiles except for `sorry` gaps into a skeleton whose gaps are standalone lemmas.

Each `sorry` is replaced by `extract_goal; sorry`; Lean prints the exact goal (with the needed context) as a
theorem statement, and the gap is then closed by applying that lemma.
"""
from __future__ import annotations

import re

from .lean import compile_lean
from .problem import Candidate, Problem, _split_decls, render

SORRY = re.compile(r"\bsorry\b")


def _is_tactic_position(line: str, col: int) -> bool:
    before = line[:col].rstrip()
    if not before.strip():
        return True
    return bool(re.search(r"(\bby|=>|·|<;>|;|\bthen|\belse)$", before))


def _rewrite_sorries(text: str, repl_tactic, repl_term) -> tuple[str, int]:
    out_lines = []
    count = 0
    for line in text.split("\n"):
        if "--" in line:
            code, comment = line.split("--", 1)
            comment = "--" + comment
        else:
            code, comment = line, ""
        pieces = []
        last = 0
        for m in SORRY.finditer(code):
            pieces.append(code[last:m.start()])
            pieces.append(repl_tactic(count) if _is_tactic_position(code, m.start()) else repl_term(count))
            count += 1
            last = m.end()
        pieces.append(code[last:])
        out_lines.append("".join(pieces) + comment)
    return "\n".join(out_lines), count


def _closer(name: str) -> str:
    return f"(first | (apply {name} <;> assumption) | (apply {name} <;> simp_all) | exact {name})"


def _sanitize(stmt: str) -> str:
    return re.sub(r"([A-Za-z_][\w']*)✝(\d*)", lambda m: f"{m.group(1)}_x{m.group(2) or ''}", stmt)


def harvest(problem: Problem, cand: Candidate):
    """Return (skeleton Candidate, [(lemma_name, statement)], order) or None.

    order is a list of ("lemma", name) / ("decl", text) items in file order (for decompose.Skeleton).
    """
    if problem.solution_defs:
        return None
    chunks = [c.strip() for c in _split_decls(cand.helpers) if c.strip()] if cand.helpers.strip() else []
    total = sum(len(SORRY.findall(re.sub(r"--[^\n]*", "", c))) for c in chunks) + \
        len(SORRY.findall(re.sub(r"--[^\n]*", "", cand.body)))
    if total == 0 or total > 8:
        return None
    probe_chunks = [_rewrite_sorries(c, lambda i: "(extract_goal; sorry)", lambda i: "(by extract_goal; sorry)")[0]
                    for c in chunks]
    probe_body, _ = _rewrite_sorries(cand.body, lambda i: "(extract_goal; sorry)", lambda i: "(by extract_goal; sorry)")
    probe = Candidate("\n\n".join(probe_chunks), probe_body, dict(cand.solutions))
    code, _ = render(problem, probe, check_axioms=False)
    res = compile_lean(code)
    if not res.ok:
        return None
    stmts = [m for m in res.messages if m.severity == "information" and re.match(r"theorem \S*extracted_", m.text)]
    stmts.sort(key=lambda m: (m.line, m.col))
    if len(stmts) != total:
        return None
    base = re.sub(r"\W", "_", problem.name)
    lemmas = []
    for i, m in enumerate(stmts):
        name = f"{base}_gap_{i + 1}"
        text = _sanitize(re.sub(r"^theorem \S+", f"theorem {name}", m.text.strip(), count=1))
        text = re.sub(r":=\s*sorry\s*$", ":=", text)
        lemmas.append((name, text))
    it = iter(lemmas)
    order: list[tuple[str, str]] = []
    out_chunks: list[str] = []
    for c in chunks:
        used: list[tuple[str, str]] = []

        def take(_i, used=used):
            nm, st = next(it)
            used.append((nm, st))
            return nm

        new_c, _ = _rewrite_sorries(c, lambda i: _closer(take(i)), lambda i: f"(by {_closer(take(i))})")
        for nm, st in used:
            order.append(("lemma", nm))
            out_chunks.append(st + " by\n  sorry")
        order.append(("decl", new_c))
        out_chunks.append(new_c)
    body_used: list[tuple[str, str]] = []

    def take_body(_i):
        nm, st = next(it)
        body_used.append((nm, st))
        return nm

    new_body, _ = _rewrite_sorries(cand.body, lambda i: _closer(take_body(i)), lambda i: f"(by {_closer(take_body(i))})")
    for nm, st in body_used:
        order.append(("lemma", nm))
        out_chunks.append(st + " by\n  sorry")
    skel = Candidate("\n\n".join(out_chunks), new_body, dict(cand.solutions))
    code2, _ = render(problem, skel, check_axioms=False)
    res2 = compile_lean(code2)
    if not res2.ok:
        return None
    return skel, lemmas, order
