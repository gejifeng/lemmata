from __future__ import annotations

import re
import textwrap
from dataclasses import dataclass

from .lean import STANDARD_AXIOMS, CompileResult, compile_lean

from .paths import BENCH_DIR as BENCH
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|sorryAx|native_decide|implemented_by|extern|unsafe|opaque)\b|@\[csimp\]|run_cmd|\belab\b|\bmacro\b|macro_rules|\bsyntax\b|\bnotation\b|#eval|#exit")


@dataclass
class Problem:
    name: str
    header: str  # imports + opens
    solution_defs: list[tuple[str, str]]  # (name, full original line(s)) with `sorry` value
    docstring: str
    statement: str  # "theorem name ... :=" (without proof)
    context: str = ""  # fixed declarations placed before the helpers (e.g. sibling lemmas)
    context_has_sorry: bool = False

    @property
    def informal(self) -> str:
        return self.docstring.strip().removeprefix("/--").removesuffix("-/").strip()

    def display(self) -> str:
        sol = "\n".join(text for _, text in self.solution_defs)
        ctx = self.context + "\n\n" if self.context else ""
        return (sol + "\n\n" if sol else "") + ctx + self.docstring + "\n" + self.statement + " by\n  sorry"


def load_putnam(name: str) -> Problem:
    text = (BENCH / f"{name}.lean").read_text(encoding="utf-8")
    return parse_problem(name, text)


def parse_problem(name: str, text: str) -> Problem:
    lines = text.splitlines()
    header_lines = [l for l in lines if l.startswith("import") or l.startswith("open")]
    header = "\n".join(header_lines)
    sol_defs: list[tuple[str, str]] = []
    for m in re.finditer(r"^((?:noncomputable )?abbrev (\S+)[^\n]*:=\s*sorry)\s*$", text, re.M):
        sol_defs.append((m.group(2), m.group(1)))
    doc_m = re.search(r"/--.*?-/", text, re.S)
    docstring = doc_m.group(0) if doc_m else ""
    thm_m = re.search(rf"^theorem {re.escape(name)}\b.*?:=\s*(?:by\s*)?\n?\s*sorry\s*$", text, re.S | re.M)
    if not thm_m:
        raise ValueError(f"cannot find theorem {name}")
    stmt = thm_m.group(0)
    stmt = re.sub(r":=\s*(?:by\s*)?\n?\s*sorry\s*$", ":=", stmt).rstrip()
    return Problem(name, header, sol_defs, docstring, stmt)


@dataclass
class Candidate:
    helpers: str  # top-level declarations before the theorem
    body: str  # tactic proof body
    solutions: dict[str, str]  # solution name -> full replacement definition


CODE_BLOCK = re.compile(r"```(?:lean4?|Lean4?)?[^\n]*\n(.*?)```", re.S)


TOP_LEVEL_DECL = re.compile(r"(?m)^(?:import|theorem|lemma|def|abbrev|example|namespace|section|noncomputable|open)\b")


def close_fences(response: str) -> str:
    """A reply cut off by the token limit may open a ```lean block without closing it."""
    if response.count("```") % 2 == 1:
        return response.rstrip() + "\n```"
    return response


def extract_candidate(problem: Problem, response: str) -> Candidate | None:
    blocks = [re.sub(r"^4[ \t]*\n", "", b) for b in CODE_BLOCK.findall(close_fences(response))]
    if not blocks:
        return None
    # prefer the last block that contains the theorem
    block = None
    for b in reversed(blocks):
        if re.search(rf"theorem\s+{re.escape(problem.name)}\b", b):
            block = b
            break
    if block is None:
        block = blocks[-1]
        # a bare tactic body only: a block with imports or top-level declarations is some other file,
        # not a proof of this theorem
        if TOP_LEVEL_DECL.search(block) or not block.strip():
            return None
        return Candidate("", _clean_body(block), {})
    return split_full_code(problem, block)


def split_full_code(problem: Problem, block: str) -> Candidate | None:
    block = re.sub(r"(?m)^\s*import\s+\S+\s*$", "", block)
    ms = list(re.finditer(rf"theorem\s+{re.escape(problem.name)}\b", block))
    if not ms:
        return None
    # if the theorem is stated several times, use the last statement that is followed by `:= by`
    m = ms[-1]
    for cand_m in reversed(ms):
        if re.search(r":=\s*by\b", block[cand_m.start():]):
            m = cand_m
            break
    before = block[: m.start()]
    rest = block[m.start():]
    # find the `:=` that ends the statement: first ":= by" or ":=" at depth 0 after the statement
    by_m = re.search(r":=\s*by\b", rest)
    if by_m:
        body = rest[by_m.end():]
    else:
        eq = rest.find(":=")
        if eq < 0:
            return None
        body = "exact " + rest[eq + 2:].strip()
    # strip trailing stuff after the proof (e.g. #print); declarations after the main theorem are moved before it
    pieces = re.split(r"\n(?=#|theorem |lemma |example |def |noncomputable |abbrev |@\[|/--)", body, maxsplit=1)
    body = pieces[0]
    trailing = pieces[1] if len(pieces) > 1 else ""
    trailing = re.sub(r"(?m)^#.*$", "", trailing)
    if trailing.strip():
        before = before + "\n\n" + trailing
    helpers_lines = []
    solutions: dict[str, str] = {}
    sol_names = {n for n, _ in problem.solution_defs}
    ctx_names = set(re.findall(r"(?:theorem|lemma|def|abbrev)\s+([^\s(:{\[]+)", problem.context))
    for chunk in _split_decls(before):
        stripped = chunk.strip()
        if not stripped:
            continue
        if stripped.startswith("import") or stripped.startswith("open ") and "\n" not in stripped:
            # opens are allowed, imports are not
            if stripped.startswith("open "):
                helpers_lines.append(stripped)
            continue
        hit = next((n for n in sol_names if re.search(rf"abbrev\s+{re.escape(n)}\b", stripped)), None)
        if hit:
            solutions[hit] = stripped
            continue
        dm = re.search(r"(?:theorem|lemma|def|abbrev)\s+([^\s(:{\[]+)", re.sub(r"^(?:--[^\n]*\n)+", "", stripped))
        if dm and dm.group(1) in ctx_names:
            continue  # restated context declaration
        # drop the docstring of the main theorem if the model repeated it
        if stripped.startswith("/--") and stripped.endswith("-/"):
            continue
        helpers_lines.append(stripped)
    return Candidate("\n\n".join(helpers_lines), _clean_body(body), solutions)


DECL_NAME = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev)\s+([^\s(:{\[]+)")


def prune_unused(cand: Candidate) -> Candidate:
    """Drop helper declarations that neither the proof body nor another kept helper refers to.
    Declarations with attributes, instances and non-declaration chunks are always kept."""
    chunks = [c.strip() for c in _split_decls(cand.helpers) if c.strip()]
    if len(chunks) <= 1:
        return cand
    named = []
    for c in chunks:
        core = re.sub(r"^(?:--[^\n]*\n|/--.*?-/\s*)+", "", c, flags=re.S).strip()
        m = DECL_NAME.match(core)
        always = core.startswith("@[") or core.startswith("instance") or m is None
        named.append((c, m.group(1) if m else None, always))
    keep = {i for i, (_, _, always) in enumerate(named) if always}
    frontier = [cand.body] + [named[i][0] for i in keep]
    changed = True
    while changed:
        changed = False
        text = "\n".join(frontier)
        for i, (c, name, _) in enumerate(named):
            if i in keep or name is None:
                continue
            short = name.rsplit(".", 1)[-1]
            if re.search(rf"(?<![\w.']){re.escape(name)}(?![\w'])", text) or re.search(rf"(?<![\w']){re.escape(short)}(?![\w'])", text):
                keep.add(i)
                frontier.append(c)
                changed = True
    kept = [named[i][0] for i in sorted(keep)]
    return Candidate("\n\n".join(kept), cand.body, cand.solutions)


def _split_decls(text: str) -> list[str]:
    parts = re.split(r"\n(?=(?:@\[|/--|theorem |lemma |def |noncomputable |abbrev |open |section|namespace|end |variable |set_option |instance |private |-- ))", "\n" + text)
    return parts


def _clean_body(body: str) -> str:
    body = body.replace("\t", "  ")
    lines = body.split("\n")
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    if not lines:
        return "sorry"
    # first line may follow `by` directly on the same line
    first = lines[0]
    rest = textwrap.dedent("\n".join(lines[1:])) if len(lines) > 1 else ""
    if first.startswith(" ") or first.startswith("\t"):
        whole = textwrap.dedent("\n".join(lines))
    else:
        whole = first.strip() + ("\n" + rest if rest else "")
    return "\n".join("  " + l if l.strip() else l for l in whole.split("\n"))


def render(problem: Problem, cand: Candidate, *, check_axioms: bool = True) -> tuple[str, int]:
    """Return (lean file text, line number where the model-controlled helpers start)."""
    parts = [problem.header, ""]
    for name, original in problem.solution_defs:
        parts.append(cand.solutions.get(name, original))
    parts.append("")
    if problem.context:
        parts.append(problem.context)
        parts.append("")
    helpers_start = sum(p.count("\n") + 1 for p in parts) + 1
    if cand.helpers:
        parts.append(cand.helpers)
        parts.append("")
    parts.append(problem.docstring)
    parts.append(problem.statement + " by")
    parts.append(cand.body)
    if check_axioms:
        parts.append("")
        parts.append(f"#print axioms {problem.name}")
    return "\n".join(parts) + "\n", helpers_start


@dataclass
class Verdict:
    solved: bool
    result: CompileResult
    code: str
    reason: str = ""


def check(problem: Problem, cand: Candidate) -> Verdict:
    code, _ = render(problem, cand)
    model_text = cand.helpers + "\n" + cand.body + "\n" + "\n".join(cand.solutions.values())
    model_text = re.sub(r"/-.*?-/", "", model_text, flags=re.S)
    model_text = re.sub(r"--[^\n]*", "", model_text)
    bad = FORBIDDEN.search(model_text)
    # solution definitions must not use sorry either
    if bad:
        res = compile_lean(code)
        return Verdict(False, res, code, f"forbidden token `{bad.group(0)}` in proof")
    for name, _ in problem.solution_defs:
        if name not in cand.solutions:
            res = compile_lean(code)
            return Verdict(False, res, code, f"the answer `{name}` is still `sorry`; you must define it")
    res = compile_lean(code)
    if not res.ok:
        return Verdict(False, res, code, "compile errors")
    if res.has_sorry and not problem.context_has_sorry:
        return Verdict(False, res, code, "proof contains sorry")
    axioms = res.axioms_of(problem.name)
    if axioms is None:
        return Verdict(False, res, code, "could not read axioms")
    allowed = STANDARD_AXIOMS | ({"sorryAx"} if problem.context_has_sorry else set())
    extra = axioms - allowed
    if extra:
        return Verdict(False, res, code, f"non-standard axioms: {sorted(extra)}")
    return Verdict(True, res, code, "ok")


def format_feedback(code: str, verdict: Verdict, max_errors: int = 6, max_chars: int = 7000) -> str:
    lines = code.split("\n")
    out = []
    if verdict.reason and verdict.reason != "compile errors":
        out.append(f"Problem: {verdict.reason}")
    errs = verdict.result.errors[:max_errors]
    for m in errs:
        src = lines[m.line - 1].strip() if 0 < m.line <= len(lines) else ""
        text = m.text
        if len(text) > 1800:
            text = text[:1800] + "\n...(truncated)"
        out.append(f"Error at line `{src}`:\n{text}")
    if len(verdict.result.errors) > max_errors:
        out.append(f"... and {len(verdict.result.errors) - max_errors} more errors")
    fb = "\n\n".join(out)[:max_chars]
    try:
        from .names import annotate_errors
        fb += annotate_errors("\n".join(m.text for m in verdict.result.errors))
    except Exception:
        pass
    return fb
