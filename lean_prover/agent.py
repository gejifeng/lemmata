from __future__ import annotations

import json
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import llm
from .problem import Candidate, Problem, Verdict, check, extract_candidate, format_feedback, prune_unused, render

SYSTEM = """\
You are an expert competition mathematician and an expert in Lean 4 with a recent Mathlib (2026, Lean v4.28).
You write complete, compiling Lean 4 proofs.

Lean/Mathlib reminders:
- This is Lean 4 syntax, NOT Lean 3: `fun x => ...`, `⟨_, _⟩`, `by` blocks with newline-separated tactics, `·` for focusing goals.
- Useful tactics: `intro`, `rcases`/`obtain`, `refine`, `constructor`, `use`, `exact`, `apply`, `have`, `calc`, `rw`, `simp`, `simp only`, `field_simp`, `ring`, `ring_nf`, `linarith`, `nlinarith [sq_nonneg (a - b), ...]`, `positivity`, `norm_num`, `omega`, `decide`, `induction n with | zero => ... | succ n ih => ...`, `Nat.strong_induction_on`, `interval_cases`, `push_cast`, `exact_mod_cast`, `gcongr`, `aesop`, `grind`, `exact?` is NOT allowed in final answers.
- Do not invent lemma names. If unsure of a Mathlib name, prove the fact directly with basic tactics, or state it as your own helper lemma and prove it.
- Natural-number subtraction truncates; integer division `/` on ℤ rounds down. Be careful with casts.
- Big operators: write `∑ i ∈ Finset.range n, f i` (NOT the deprecated `∑ i in s, f i`). Same for `∏`.
- Casts: old names `Int.coe_nat_*`, `Nat.cast_*` variants were renamed to `Int.natCast_*`/`Nat.cast_*`; prefer `push_cast`, `norm_cast`, `exact_mod_cast`, `omega` instead of cast lemma names.
- `induction n with` case names are `zero` and `succ`; for ℤ use `Int.induction_on` or reduce to ℕ via `Int.toNat_of_nonneg` / `Int.eq_ofNat_of_zero_le`.
- Use `Finset.sum_range_succ`, `Finset.sum_Icc_succ_top`, `Finset.prod_range_succ` for sums; `decide` only works for small closed computations.
- For a goal `A ↔ B`, `constructor` produces first `A → B` (mp) and then `B → A` (mpr). Destructuring an equation
  hypothesis `h : f = g` with `obtain`/`rcases`/`subst` eliminates the variable `f`; use `rw [h]` or `subst` deliberately.
- In `calc`, write each step's justification on the same line (`_ = b := by ring`) or indent its tactic block deeper
  than the start of that step's term; otherwise Lean reports "expected '{' or indented tactic sequence".
- `admit`, `axiom`, `native_decide` are forbidden. Aim for a complete proof; if one or two intermediate steps are
  genuinely hard, you may leave exactly those steps as `sorry` (they will be proved separately), but everything
  else must compile.

Mathlib search: if you need a lemma whose exact name you do not know, you may output a ```search block with one query
per line (a natural-language description of the fact, or a Loogle pattern such as `Nat.choose, Nat.ModEq`). The system
runs the queries and returns real declarations from this Mathlib version together with your Lean feedback.

Be efficient: settle on a proof idea quickly, prefer the most elementary and formalization-friendly argument,
and keep your private reasoning under about 8000 tokens. Do not write the whole proof twice in your head.

Output format: think the mathematics through first. Then output exactly ONE ```lean code block containing
any helper lemmas you need (each fully proved) followed by the main theorem with its statement copied EXACTLY as given and its proof.
Do not include `import` lines. Keep the theorem statement unchanged.
"""


def initial_prompt(problem: Problem, hint: str = "", premises: str = "", plan: str = "", previous: dict | None = None) -> str:
    sol_note = ""
    if problem.solution_defs:
        names = ", ".join(n for n, _ in problem.solution_defs)
        sol_note = (f"\nThe answer {names} is currently `sorry`: you must determine the correct value and include a full "
                    f"definition (e.g. `noncomputable abbrev {problem.solution_defs[0][0]} : ... := <value>`) in your code block before the theorem.\n")
    if problem.context:
        sol_note += ("\nAll declarations shown above the target theorem are ALREADY available in the file; "
                     "use them freely but do NOT repeat or re-prove them. Prove ONLY the target theorem "
                     f"`{problem.name}`; other parts of the overall argument are handled separately.\n")
    hint_txt = f"\nHint / proof plan from a colleague (may be incomplete):\n{hint}\n" if hint else ""
    plan_txt = (f"\nInformal proof and formalization notes already worked out for this theorem (follow them unless "
                f"they are wrong):\n{plan}\n") if plan else ""
    prem_txt = f"\n{premises}\n" if premises else ""
    prev_txt = ""
    if previous:
        prev_txt = ("\nAn earlier attempt (from a previous run) came close. Its code and Lean's errors:\n```lean\n"
                    + previous["code"].split("#print axioms")[0][-6000:] + "\n```\nErrors:\n" + previous["feedback"][:3000] + "\n")
    return f"""Prove the following theorem in Lean 4 with Mathlib.

```lean
{problem.header}

{problem.display()}
```
{sol_note}{hint_txt}{plan_txt}{prem_txt}{prev_txt}
First work out a rigorous informal proof, choosing an approach that is easy to formalize. Then write the Lean code.
"""


@dataclass
class Attempt:
    chain: int
    round: int
    verdict_reason: str
    solved: bool
    feedback: str
    response_tokens: int
    seconds: float
    code: str
    raw: str = ""


@dataclass
class ProblemState:
    problem: Problem
    out_dir: Path
    solved: bool = False
    proof_code: str | None = None
    attempts: list[Attempt] = field(default_factory=list)
    solved_candidate: Candidate | None = None
    harvested: list = field(default_factory=list)  # (skeleton Candidate, lemmas, order) from sorry-gapped attempts
    lock: threading.Lock = field(default_factory=threading.Lock)
    harvest_seen: set = field(default_factory=set)
    premises: str | None = None  # rendered search results, computed once
    plan: str | None = None  # informal proof + formalization notes (two-stage mode), computed once
    best_errors: int | None = None  # fewest compiler errors seen so far (progress signal)
    stalled_rounds: int = 0  # consecutive think rounds without improving best_errors
    stalled: bool = False
    prep_lock: threading.Lock = field(default_factory=threading.Lock)

    def note_errors(self, n: int) -> bool:
        """Record an attempt's error count; True if it is a new best."""
        with self.lock:
            if self.best_errors is None or n < self.best_errors:
                self.best_errors = n
                return True
            return False

    def record(self, a: Attempt) -> None:
        with self.lock:
            self.attempts.append(a)
            with (self.out_dir / "attempts.jsonl").open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(a.__dict__, ensure_ascii=False) + "\n")
            if a.solved and not self.solved:
                self.solved = True
                self.proof_code = a.code
                (self.out_dir / "proof.lean").write_text(a.code, encoding="utf-8")


from .paths import CONFIG_FILE


DEFAULT_CONFIG = {
    "stall_rounds": 2,            # think rounds without fewer errors before decomposing
    "race_top": False,            # run decomposition in parallel with direct attempts at the top level
    "parallel_sketches": 1,       # decomposition workers at the top level
    "quick_repairs": 4,           # non-thinking repair requests after each thinking attempt
    "repair_samples": 2,          # samples per repair request (vLLM `n`)
    "think_max_tokens": 14000,
    "repair_max_tokens": 6000,
    "search": True,               # LeanSearch/Loogle premise retrieval
    "two_stage": False,           # write an informal plan before formalizing (costly; off by default)
    "two_stage_max_depth": 1,
    "plan_max_tokens": 14000,
    "formalize_max_tokens": 10000,
    "fair_share_calls": 3,        # priority drops by 1 for every N model calls a top-level problem has used
    "depth_weight": 2,            # priority bonus per decomposition level
    "resume_previous": True,      # start from the best earlier attempt on the same statement
    "lemma_cache": True,          # reuse lemmas proved in earlier runs
}


def runtime_config() -> dict:
    """Tunable knobs (see config/default.json), re-read on every use so a running campaign can be adjusted."""
    cfg = dict(DEFAULT_CONFIG)
    try:
        cfg.update(json.loads(CONFIG_FILE.read_text(encoding="utf-8")))
    except (OSError, ValueError):
        pass
    return cfg


def _evaluate(state: ProblemState, chain_id: int, rnd: int, content: str, resp, mode: str):
    """Returns (solved, feedback, code_or_None)."""
    problem = state.problem
    if content.count("```") % 2 == 1:
        content = content + "\n```"
    cand = extract_candidate(problem, content)
    if cand is None:
        fb = ("Your answer did not contain a ```lean code block with the theorem. "
              "Output exactly one ```lean block with helper lemmas and the full theorem with proof.")
        if resp.finish_reason == "length":
            fb = "You ran out of output budget before producing code. Think more concisely and output the ```lean block."
        state.record(Attempt(chain_id, rnd, f"{mode}: no code", False, fb, resp.completion_tokens, resp.seconds, "",
                             raw=content))
        return False, fb, None
    cand = prune_unused(cand)
    verdict = check(problem, cand)
    if not verdict.solved and verdict.result.errors and "forbidden" not in verdict.reason:
        try:
            from .autopatch import remove_dead_tactics
            from .problem import split_full_code
            _, start = render(problem, cand)
            out = remove_dead_tactics(verdict.code, verdict.result.errors, start)
            if out is not None:
                new_cand = split_full_code(problem, out[0].split("#print axioms")[0])
                if new_cand is not None:
                    v2 = check(problem, new_cand)
                    if v2.solved or len(v2.result.errors) < len(verdict.result.errors):
                        cand, verdict = new_cand, v2
                        mode = mode + "+deadtac"
        except Exception:
            pass
    if not verdict.solved and verdict.result.errors and "forbidden" not in verdict.reason:
        try:
            from .autopatch import try_autopatch
            from .problem import split_full_code
            _, start = render(problem, cand)
            out = try_autopatch(verdict.code, verdict.result.errors, start)
            if out is not None and out[1].ok:
                patched_cand = split_full_code(problem, out[0].split("#print axioms")[0])
                if patched_cand is not None:
                    v2 = check(problem, patched_cand)
                    if v2.solved:
                        cand, verdict = patched_cand, v2
                        mode = mode + "+autopatch"
        except Exception:
            pass
    fb = "" if verdict.solved else format_feedback(verdict.code, verdict)
    if not verdict.solved:
        state.note_errors(len(verdict.result.errors) + (1 if "sorry" in verdict.reason else 0))
        if runtime_config().get("search"):
            fb += error_search(verdict)
    if not verdict.solved and "sorry" in verdict.reason and verdict.result.ok:
        try:
            from .harvest import harvest
            h = harvest(problem, cand)
        except Exception:
            h = None
        if h is not None:
            key = h[0].helpers + "\n" + h[0].body
            with state.lock:
                if key not in state.harvest_seen:
                    state.harvest_seen.add(key)
                    state.harvested.append(h)
            fb += ("\n\nNote: apart from the `sorry` gaps your proof compiles; the gaps have been recorded as "
                   "separate lemmas. You may still try to fill them in directly.")
    if verdict.solved:
        with state.lock:
            if state.solved_candidate is None:
                state.solved_candidate = cand
    state.record(Attempt(chain_id, rnd, f"{mode}: {verdict.reason}", verdict.solved, fb, resp.completion_tokens,
                         resp.seconds, verdict.code, raw=content))
    shown, _ = render(problem, cand, check_axioms=False)
    return verdict.solved, fb, shown


def error_search(verdict: Verdict) -> str:
    """For unknown identifiers, search Mathlib by the intent encoded in the (wrong) name."""
    import re
    from . import search
    idents = []
    for m in verdict.result.errors:
        for g in re.findall(r"Unknown (?:identifier|constant) [`'«]?([\w.'₀-₉]+)", m.text):
            if ("." in g or "_" in g) and g not in idents:
                idents.append(g)
    if not idents:
        return ""
    queries = []
    for g in idents[:3]:
        words = re.sub(r"[._]", " ", g)
        queries.append(words)
    try:
        prems = search.search(queries, k=4, limit=8)
    except Exception:
        return ""
    txt = search.render_premises(prems, "Mathlib search for the intent of the unknown names (verified to exist):")
    return ("\n\n" + txt) if txt else ""


PLAN_PROMPT = """Here is a theorem to be proved in Lean 4 with Mathlib.

```lean
{header}

{display}
```
{hint}{premises}
Do NOT write Lean code yet. Write:
1. A complete, rigorous informal proof, as elementary and formalization-friendly as possible, with every step justified.
2. Formalization notes: the order of `have` steps you would use, the key Mathlib lemmas or tactics for each step
   (only names you are sure exist, or describe the fact), and pitfalls (casts, ℕ subtraction, division, edge cases).
Be concise: at most about 60 lines in total.
"""


def ensure_prep(state: ProblemState, hint: str, priority: int, stop, depth: int = 0) -> None:
    """Compute premises (search) and, in two-stage mode, the informal plan, once per problem state."""
    cfg = runtime_config()
    with state.prep_lock:
        if state.premises is None:
            state.premises = ""
            if cfg.get("search"):
                try:
                    from . import search
                    qs = search.propose_queries(state.problem.statement + ("\n" + hint[-1500:] if hint else ""),
                                                priority=priority + 2)
                    prems = search.search(qs, k=5, limit=14)
                    state.premises = search.render_premises(prems)
                    (state.out_dir / "premises.txt").write_text("queries: " + json.dumps(qs, ensure_ascii=False)
                                                                + "\n\n" + state.premises, encoding="utf-8")
                except Exception as exc:  # search is optional
                    state.premises = ""
        if state.plan is None and cfg.get("two_stage") and depth <= int(cfg.get("two_stage_max_depth", 1)):
            state.plan = ""
            if stop():
                return
            prompt = PLAN_PROMPT.format(header=state.problem.header, display=state.problem.display(),
                                        hint=(f"\nContext from the overall proof:\n{hint[-2500:]}\n" if hint else ""),
                                        premises=(f"\n{state.premises}\n" if state.premises else ""))
            try:
                r = llm.chat_salvage([{"role": "system", "content": "You are an expert competition mathematician who also knows Lean 4 and Mathlib well."},
                                      {"role": "user", "content": prompt}],
                                     max_tokens=int(cfg["plan_max_tokens"]), temperature=0.6, stop_check=stop,
                                     final_instruction="Write the informal proof and formalization notes now (no Lean code).",
                                     prefill=None, priority=priority)
            except llm.LLMFailure:
                return
            if r.finish_reason != "cancelled":
                state.plan = r.content.strip()[-6000:]
                (state.out_dir / "plan.md").write_text(state.plan, encoding="utf-8")
                (state.out_dir / "plan_tokens.json").write_text(json.dumps({"tokens": r.completion_tokens}), encoding="utf-8")


def run_chain(state: ProblemState, chain_id: int, rounds: int, hint: str = "", temperature: float = 0.8,
              max_tokens: int = 14000, deadline: float | None = None, cancelled=None, priority: int = 0,
              stall_rounds: int | None = None, depth: int = 0, root: dict | None = None) -> bool:
    """Direct proof attempts. Returns True if solved. Sets state.stalled when `stall_rounds` consecutive think rounds
    did not reduce the best error count (the caller may then decompose instead)."""
    from . import search
    problem = state.problem
    cfg = runtime_config()

    def stop() -> bool:
        return state.solved or (deadline is not None and time.time() > deadline) or \
            (cancelled is not None and cancelled())

    root = root if root is not None else {"calls": 0}
    ensure_prep(state, hint, priority - root["calls"], stop, depth=depth)
    previous = None
    if cfg.get("resume_previous") and chain_id == 0:
        try:
            from .history import best_previous
            previous = best_previous(problem)
        except Exception:
            previous = None
    messages = [
        {"role": "system", "content": SYSTEM},
        {"role": "user", "content": initial_prompt(problem, hint, premises=state.premises or "", plan=state.plan or "",
                                                   previous=previous)},
    ]
    stall_limit = stall_rounds if stall_rounds is not None else int(cfg.get("stall_rounds", 0) or 0)

    def prio() -> int:
        # progress-aware: stalled problems yield to ones that are moving;
        # fair share: top-level problems that already used many calls yield to untouched ones
        return priority - min(state.stalled_rounds, 3) - root["calls"] // int(cfg.get("fair_share_calls", 1))

    search_results = ""
    for rnd in range(1, rounds + 1):
        if stop():
            return state.solved
        cfg = runtime_config()
        before = state.best_errors
        think_budget = int(cfg["formalize_max_tokens"] if state.plan else cfg["think_max_tokens"])
        if search_results:
            messages.append({"role": "user", "content": search_results + "\n\nNow write the proof."})
            search_results = ""
        try:
            resp = llm.chat_salvage(messages, max_tokens=think_budget, temperature=temperature,
                                    final_instruction="Output exactly one ```lean block with helper lemmas and the full theorem with proof.",
                                    stop_check=stop, priority=prio())
        except llm.LLMFailure as exc:
            state.record(Attempt(chain_id, rnd, f"llm failure: {exc}", False, "", 0, 0.0, ""))
            return False
        root["calls"] += 1
        if resp.finish_reason == "cancelled":
            return state.solved
        sr = search.run_search_blocks(resp.content) if cfg.get("search") else ""
        solved, fb, code = _evaluate(state, chain_id, rnd, resp.content, resp, "think")
        if solved:
            return True
        if sr:
            fb = (fb + "\n\n" + sr) if code is not None else sr
        last_assistant = resp.content[-8000:] or "(no answer)"
        # cheap non-thinking repairs of the concrete compiler errors, several samples per request
        if code is not None:
            for q in range(int(cfg["quick_repairs"])):
                if stop():
                    return state.solved
                repair_msgs = messages + [
                    {"role": "assistant", "content": "```lean4\n" + code + "\n```"},
                    {"role": "user", "content": "Lean rejected this code. Compiler output:\n\n" + fb +
                     "\n\nRepair these specific errors with minimal changes. Output the complete corrected code "
                     "(helpers + full theorem) in one ```lean block, no explanation."},
                ]
                try:
                    samples = llm.chat_n(repair_msgs, int(cfg.get("repair_samples", 1)),
                                         max_tokens=int(cfg["repair_max_tokens"]), temperature=0.4 + 0.2 * q,
                                         prefill="```lean4\n", priority=prio() + 1, stop_check=stop)
                except llm.LLMFailure:
                    break
                root["calls"] += 1
                if samples and samples[0].finish_reason == "cancelled":
                    return state.solved
                best = None
                for r2 in samples:
                    solved, fb2, code2 = _evaluate(state, chain_id, rnd, r2.content, r2, f"repair{q+1}")
                    if solved:
                        return True
                    if code2 is None or code2 == code:
                        continue
                    from .history import error_count
                    score = error_count(fb2)
                    if best is None or score < best[0]:
                        best = (score, code2, fb2)
                if best is None:
                    break  # nothing new: go back to thinking
                _, code, fb = best
                last_assistant = "```lean\n" + code + "\n```"
        improved = before is None or (state.best_errors is not None and state.best_errors < before)
        with state.lock:
            state.stalled_rounds = 0 if improved else state.stalled_rounds + 1
            if stall_limit and state.stalled_rounds >= stall_limit:
                state.stalled = True
        messages.append({"role": "assistant", "content": last_assistant})
        messages.append({"role": "user", "content": (
            "Lean rejected this attempt. Compiler output:\n\n" + fb +
            "\n\nFix the proof. If the approach is fundamentally stuck, change approach. "
            "Output the complete corrected code in one ```lean block (helpers + full theorem).")})
        # keep context bounded: drop old rounds but keep system + task
        if len(messages) > 8:
            messages = messages[:2] + messages[-6:]
        if state.stalled:
            return state.solved
    return state.solved
