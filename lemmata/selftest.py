"""Offline end-to-end self-test of the solve() pipeline with a scripted fake model (no LLM calls, real Lean).

    python -m lemmata.selftest
"""
from __future__ import annotations

import shutil
import time

from . import agent, decompose, llm, search
from .llm import LLMResponse
from .formalize import formalize
from .problem import Problem, check_statement, parse_lean_problem

from .paths import RUNS_DIR

OUT = RUNS_DIR / "selftest"


def R(text: str) -> LLMResponse:
    return LLMResponse(text, "", 100, "stop", 0.01)


class Script:
    """Fake model: picks a reply by matching the prompt."""

    def __init__(self, rules):
        self.rules = rules
        self.log: list[str] = []

    def reply(self, messages) -> str:
        text = "\n".join(m["content"] for m in messages if isinstance(m.get("content"), str))
        for key, val in self.rules:
            if key in text:
                self.log.append(key)
                return val(text) if callable(val) else val
        self.log.append("<default>")
        return "I cannot do this."

    def install(self):
        def chat(messages, **kw):
            return R(self.reply(messages))

        def chat_n(messages, n, **kw):
            return [R(self.reply(messages)) for _ in range(n)]

        def chat_salvage(messages, **kw):
            return R(self.reply(messages))

        llm.chat = chat
        llm.chat_n = chat_n
        llm.chat_salvage = chat_salvage
        search.propose_queries = lambda statement, extra="", priority=0: ["sum of two squares"]


def run_case(name: str, problem: Problem, rules, expect_solved: bool, **kw) -> bool:
    script = Script(rules)
    script.install()
    d = OUT / name
    shutil.rmtree(d, ignore_errors=True)
    events = []
    t = time.time()
    cand = decompose.solve(problem, d, 0, chains=1, rounds=kw.get("rounds", 3), max_depth=kw.get("max_depth", 2),
                           sketches=kw.get("sketches", 2), deadline=time.time() + 900, log=events.append,
                           seed_skeletons=[])
    ok = (cand is not None) == expect_solved
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: solved={cand is not None} ({time.time() - t:.0f}s)")
    for e in events:
        print("      ", e)
    if not ok:
        print("       model calls:", script.log)
    return ok


def main() -> None:
    agent.runtime_config = lambda: {
        "quick_repairs": 2, "think_max_tokens": 1000, "repair_max_tokens": 500, "repair_samples": 2,
        "search": True, "two_stage": True, "plan_max_tokens": 1000, "formalize_max_tokens": 1000,
        "stall_rounds": 2, "resume_previous": False, "parallel_sketches": 2,
    }
    results = []

    # 1. repair path: first attempt has a wrong rewrite, a repair sample fixes it
    p1 = Problem("st1", "import Mathlib", [], "", "theorem st1 (S : Type*) [Mul S] (hS : ∀ a b : S, (a * b) * a = b) "
                 "(a b : S) : a * (b * a) = b :=")
    bad = "```lean\ntheorem st1 (S : Type*) [Mul S] (hS : ∀ a b : S, (a * b) * a = b) (a b : S) : a * (b * a) = b := by\n  exact hS a b\n```"
    good = "```lean\ntheorem st1 (S : Type*) [Mul S] (hS : ∀ a b : S, (a * b) * a = b) (a b : S) : a * (b * a) = b := by\n  have h := hS (b * a) b\n  rwa [hS b a] at h\n```"
    decompose.try_automation = lambda p: None  # force the model path in this case
    results.append(run_case("repair", p1, [
        ("Do NOT write Lean code yet", "Plan: instantiate hS twice."),
        ("Repair these specific errors", good),
        ("Prove the following theorem", bad),
    ], True))

    # 2. stall -> decomposition with a lemma-free (complete) skeleton
    results.append(run_case("stall_to_complete_skeleton", p1, [
        ("Do NOT write Lean code yet", "Plan."),
        ("Design a proof skeleton", good),
        ("Repair these specific errors", bad),
        ("Prove the following theorem", bad),
    ], True, rounds=4))

    # 3. decomposition where one lemma is false (plausible) and the second sketch works
    p3 = Problem("st3", "import Mathlib", [], "", "theorem st3 (n : ℕ) (h : 3 ≤ n) : n ^ 2 ≥ 2 * n + 1 :=")
    false_sketch = """```lean
theorem st3_l1 (n : ℕ) : n ^ 2 ≥ 2 * n + 1 := by
  sorry

theorem st3 (n : ℕ) (h : 3 ≤ n) : n ^ 2 ≥ 2 * n + 1 := by
  exact st3_l1 n
```"""
    true_sketch = """```lean
theorem st3_l2 (n : ℕ) (h : 3 ≤ n) : n * n ≥ 3 * n := by
  sorry

theorem st3 (n : ℕ) (h : 3 ≤ n) : n ^ 2 ≥ 2 * n + 1 := by
  have := st3_l2 n h
  nlinarith
```"""
    l2_proof = "```lean\ntheorem st3_l2 (n : ℕ) (h : 3 ≤ n) : n * n ≥ 3 * n := by\n  exact Nat.mul_le_mul_right n h\n```"
    import itertools
    sk_iter = itertools.cycle([false_sketch, true_sketch])
    results.append(run_case("false_lemma_then_resketch", p3, [
        ("Do NOT write Lean code yet", "Plan."),
        ("Design a proof skeleton", lambda t: true_sketch if "FALSE" in t else next(sk_iter)),
        ("theorem st3_l2", l2_proof),
        ("Prove the following theorem", "no idea"),
    ], True, rounds=2, sketches=3))

    # 4. harvest: the direct attempt compiles except for one sorry; the gap lemma is solved by automation
    decompose.try_automation = _real_automation
    p4 = Problem("st4", "import Mathlib", [], "", "theorem st4 (x : ℝ) (hx : 0 < x) : x / (x + 1) < 1 ∧ 0 < x + 1 :=")
    gapped = "```lean\ntheorem st4 (x : ℝ) (hx : 0 < x) : x / (x + 1) < 1 ∧ 0 < x + 1 := by\n  have h1 : 0 < x + 1 := by linarith\n  have h2 : x / (x + 1) < 1 := by\n    sorry\n  exact ⟨h2, h1⟩\n```"
    results.append(run_case("harvest_gap", p4, [
        ("Do NOT write Lean code yet", "Plan."),
        ("Design a proof skeleton", "no skeleton"),
        ("theorem st4_gap_1", lambda t: "```lean\n" + t[t.index("theorem st4_gap_1"):].split(":= by")[0]
         + ":= by\n  rw [div_lt_one (by linarith)]\n  linarith\n```"),
        ("Prove the following theorem", gapped),
        ("Repair these specific errors", gapped),
    ], True, rounds=2))

    # 5. a user's Lean file with a definition, parsed and checked
    src = ("import Mathlib\n\ndef my_sq (n : ℕ) : ℕ := n * n\n\n/-- Squares of even numbers are even. -/\n"
           "theorem st5 (n : ℕ) (h : Even n) : Even (my_sq n) := by\n  sorry\n")
    p5 = parse_lean_problem(src)
    ok5 = p5.name == "st5" and "def my_sq" in p5.context and check_statement(p5)[0]
    try:
        parse_lean_problem(src.replace("def my_sq", "axiom ax : False\ndef my_sq"))
        ok5 = False
    except ValueError:
        pass
    print(f"[{'PASS' if ok5 else 'FAIL'}] lean_file_problem")
    results.append(ok5)

    # 6. natural language -> Lean: the first statement does not compile, the retry does
    stmt = "theorem st6 (n : ℤ) : 6 ∣ n ^ 3 - n := by\n  sorry"
    Script([
        ("Lean rejected this statement", "```lean\nimport Mathlib\n\n" + stmt + "\n```\nNOTES: none"),
        ("Explain precisely what this theorem claims", "For every integer n, 6 divides n^3 - n."),
        ("Translate the following", "```lean\nimport Mathlib\n\n" + stmt.replace("ℤ)", "ℤ") + "\n```\nNOTES: none"),
    ]).install()
    r6 = formalize("Prove that n^3 - n is divisible by 6 for every integer n.")
    ok6 = r6["ok"] and r6["attempts"] == 2 and r6["name"] == "st6" and "6 divides" in r6["meaning"]
    print(f"[{'PASS' if ok6 else 'FAIL'}] formalize_retry: attempts={r6['attempts']} ok={r6['ok']}")
    results.append(ok6)

    print(f"\n{sum(results)}/{len(results)} self-tests passed")


_real_automation = decompose.try_automation

if __name__ == "__main__":
    main()
