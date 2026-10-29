"""Natural language -> Lean theorem statement, for a human to confirm before anything is proved.

    python -m lemmata.formalize "Prove that n^3 - n is divisible by 6 for every integer n."

The model writes a Lean file that states the problem with `sorry` as the proof; it must compile (errors are fed
back, up to `attempts` times). A second, independent request sees only the Lean code and explains what it
literally says, so a reader can compare that explanation with the original problem. Formalization is the one
step Lean cannot check: a proof is only ever a proof of the Lean statement.
"""
from __future__ import annotations

import re
import sys

from . import llm
from .problem import CODE_BLOCK, close_fences, check_statement, parse_lean_problem

SYSTEM = "You are an expert in Lean 4 and Mathlib who translates mathematics into faithful formal statements."

PROMPT = """Translate the following mathematics problem into a Lean 4 theorem statement (Lean v4.28, current Mathlib).
Do NOT prove it: the proof must be `sorry`.

Problem:
{problem}

Rules:
- The file starts with `import Mathlib`. You may add `open ...` lines and, only if really needed, `def` /
  `noncomputable def` definitions (complete, without `sorry`). No `axiom`, `namespace`, `section` or `variable`.
- The file ends with exactly one goal: `theorem <snake_case_name> ... := by\\n  sorry`.
- If the problem asks to find, compute or determine something, put the answer you believe is correct into the
  statement itself (e.g. `... = 42`, or `{{n : ℕ | ...}} = {{1, 2}}`, or an `↔` characterizing all solutions).
- Faithfulness first: keep every hypothesis, do not weaken or strengthen the claim, and choose the number types the
  problem means (ℕ, ℤ, ℚ, ℝ, ℂ). Natural-number subtraction and `/` on ℕ and ℤ truncate; cast when needed.
- Make the statement non-vacuous: hypotheses must be satisfiable, as in the problem.

Answer with one ```lean block containing the whole file, then a line starting with `NOTES:` listing any ambiguity in
the problem and the choices you made (or `NOTES: none`)."""

RETRY = """Lean rejected this statement:

{errors}

Fix the statement (it must compile with `sorry` as the proof) and answer in the same format."""

EXPLAIN = """Here is a Lean 4 theorem statement (Mathlib):

```lean
{code}
```

Explain precisely what this theorem claims, reading the Lean code literally: the objects and their types, every
hypothesis, and the conclusion (including any specific answer it asserts). Do not guess what was intended and do
not judge whether it is true. Write {language}, in at most 8 short sentences or bullet points, with formulas in
plain text or LaTeX."""


def _language(text: str) -> str:
    return "in Chinese (简体中文)" if re.search(r"[一-鿿]", text) else "in English"


def _extract(reply: str) -> tuple[str, str]:
    blocks = CODE_BLOCK.findall(close_fences(reply))
    code = next((b for b in reversed(blocks) if "theorem" in b), blocks[-1] if blocks else "")
    code = re.sub(r"^4[ \t]*\n", "", code).strip()
    notes_m = re.search(r"NOTES:\s*(.*)", reply, re.S)
    notes = notes_m.group(1).strip() if notes_m else ""
    if notes.lower().rstrip(".") == "none":
        notes = ""
    return code, notes


def explain(code: str, language: str) -> str:
    r = llm.chat([{"role": "user", "content": EXPLAIN.format(code=code, language=language)}],
                 max_tokens=1500, temperature=0.2, thinking=False)
    return r.content.strip()


def formalize(text: str, *, attempts: int = 3, log=lambda msg: None) -> dict:
    """Returns {ok, lean, name, meaning, notes, errors, attempts}. `ok` means the statement compiles."""
    messages = [{"role": "system", "content": SYSTEM}, {"role": "user", "content": PROMPT.format(problem=text.strip())}]
    out = {"ok": False, "lean": "", "name": "", "meaning": "", "notes": "", "errors": "", "attempts": 0}
    for i in range(attempts):
        out["attempts"] = i + 1
        log(f"formalizing (attempt {i + 1}/{attempts})")
        r = llm.chat_salvage(messages, max_tokens=12000, temperature=0.4, prefill=None,
                             final_instruction="Output the ```lean block and the NOTES: line now.")
        code, notes = _extract(r.content)
        out.update(lean=code, notes=notes)
        if not code:
            errors = "No ```lean block was found in your answer."
        else:
            try:
                problem = parse_lean_problem(code, informal=text)
                log("checking the statement with Lean")
                ok, errors = check_statement(problem)
                if ok:
                    out.update(ok=True, name=problem.name, errors="")
                    break
            except ValueError as exc:
                errors = str(exc)
        out["errors"] = errors
        log("Lean rejected the statement" + (", retrying" if i + 1 < attempts else ""))
        messages += [{"role": "assistant", "content": r.content}, {"role": "user", "content": RETRY.format(errors=errors)}]
    if out["lean"]:
        log("explaining the Lean statement independently")
        try:
            out["meaning"] = explain(out["lean"], _language(text))
        except llm.LLMFailure as exc:
            out["meaning"] = f"(explanation failed: {exc})"
    return out


def main() -> None:
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    text = " ".join(sys.argv[1:])
    res = formalize(text, log=lambda m: print(f"[{m}]", file=sys.stderr, flush=True))
    print(res["lean"])
    print("\n-- " + ("compiles" if res["ok"] else "does NOT compile:\n" + res["errors"]))
    if res["meaning"]:
        print("\nWhat the Lean statement says:\n" + res["meaning"])
    if res["notes"]:
        print("\nNotes:\n" + res["notes"])


if __name__ == "__main__":
    main()
