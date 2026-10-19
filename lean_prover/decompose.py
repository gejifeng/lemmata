from __future__ import annotations

import json
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

from . import llm
from .agent import SYSTEM, ProblemState, run_chain
from .problem import Candidate, Problem, _split_decls, check, extract_candidate, format_feedback, render
from .lean import compile_lean

SKETCH_SYSTEM = SYSTEM.replace(
    "You write complete, compiling Lean 4 proofs.",
    "You design Lean 4 proof skeletons: a decomposition of a hard theorem into helper lemmas.",
)

SKETCH_PROMPT = """We want to prove the following theorem in Lean 4 with Mathlib, but direct attempts failed.

```lean
{header}

{display}
```
{failures}{extra}
Design a proof skeleton:
1. First write a careful, rigorous informal proof.
2. Then write ONE ```lean code block containing:
   - any `def`s you need,
   - several helper lemmas (`theorem name ... := by sorry`), each a self-contained, clearly TRUE, precisely stated
     intermediate fact, small enough to be proved in roughly 5-30 lines of Lean. Prefer 2-6 lemmas.
   - the main theorem (statement copied EXACTLY) whose proof is COMPLETE (no sorry) and uses only the helper lemmas,
     Mathlib and simple tactics.
Every helper lemma statement must be fully explicit (all variables bound as arguments, with all needed hypotheses).
Double-check every lemma is actually true including edge cases (n = 0, empty sets, truncated subtraction, division by zero).
The skeleton must compile with only the helper lemma proofs being `sorry`.
"""


@dataclass
class Skeleton:
    candidate: Candidate
    context_decls: list[str]  # non-lemma declarations (defs, opens) in order
    lemmas: list[tuple[str, str]]  # (name, statement "theorem name ... :=") in order
    order: list[tuple[str, str]]  # ("decl", text) or ("lemma", name) in original order
    prose: str


LEMMA_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(theorem|lemma)\s+([^\s(:{\[]+)(.*?):=\s*(?:by\s*)?(?:\n\s*)?sorry\s*$", re.S)


def parse_skeleton(problem: Problem, response: str) -> Skeleton | None:
    cand = extract_candidate(problem, response)
    if cand is None:
        return None
    context, lemmas, order = [], [], []
    for chunk in _split_decls(cand.helpers):
        s = chunk.strip()
        if not s:
            continue
        # strip leading comments
        body = re.sub(r"^(?:--[^\n]*\n)+", "", s).strip()
        m = LEMMA_RE.match(body)
        if m:
            name = m.group(2)
            stmt = f"theorem {name}{m.group(3).rstrip()} :="
            lemmas.append((name, stmt))
            order.append(("lemma", name))
        else:
            context.append(s)
            order.append(("decl", s))
    prose = CODE_BLOCK_STRIP.sub("", response).strip()
    return Skeleton(cand, context, lemmas, order, prose[-4000:])


CODE_BLOCK_STRIP = re.compile(r"```.*?```", re.S)


def prepare_skeleton(problem: Problem, response: str) -> Skeleton | None:
    """parse_skeleton + turn gaps in the main proof into lemmas when possible."""
    sk = parse_skeleton(problem, response)
    if sk is None:
        return None
    if re.search(r"\bsorry\b", re.sub(r"--[^\n]*", "", sk.candidate.body)):
        absorbed = absorb_body_sorries(problem, sk)
        if absorbed is not None:
            return absorbed
    return sk


def absorb_body_sorries(problem: Problem, sk: Skeleton) -> Skeleton | None:
    """`sorry`s left in the main proof become extra lemmas: Lean states each gap via `extract_goal`."""
    from .harvest import harvest
    if problem.solution_defs and not sk.candidate.solutions:
        return None
    helpers_text = sk.candidate.helpers
    ctx = "\n\n".join(t for t in [problem.context, helpers_text] if t)
    host = Problem(problem.name, problem.header, [], problem.docstring, problem.statement,
                   context=ctx, context_has_sorry=True)
    sol_block = "\n".join(sk.candidate.solutions.get(n, o) for n, o in problem.solution_defs)
    if sol_block:
        host.context = sol_block + "\n\n" + host.context
    h = harvest(host, Candidate("", sk.candidate.body, {}))
    if h is None:
        return None
    hskel, hlemmas, horder = h
    cand = Candidate("\n\n".join(t for t in [helpers_text, hskel.helpers] if t), hskel.body,
                     dict(sk.candidate.solutions))
    return Skeleton(cand, list(sk.context_decls), list(sk.lemmas) + hlemmas,
                    list(sk.order) + [("lemma", n) for n, _ in hlemmas], sk.prose)


def _conclusion(stmt: str) -> str:
    """The part of a theorem statement after its binders (rough: after the last top-level ' : ')."""
    t = re.sub(r"\s+", " ", stmt).strip().removesuffix(":=").strip()
    depth = 0
    cut = -1
    for i, ch in enumerate(t):
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            depth -= 1
        elif ch == ":" and depth == 0 and t[i - 1:i + 2] == " : ":
            cut = i
    return t[cut + 1:].strip() if cut >= 0 else t


def validate_skeleton(problem: Problem, sk: Skeleton) -> str | None:
    """Return None if OK, else feedback. Skeletons whose main proof still has `sorry` are handled by the caller
    (absorb_body_sorries) before this is called."""
    if re.search(r"\bsorry\b", re.sub(r"--[^\n]*", "", sk.candidate.body)):
        return ("The main theorem's proof must compile; any `sorry` left in it must sit at a position where the "
                "surrounding proof still type-checks.")
    if not sk.lemmas:
        v = check(problem, sk.candidate)
        if v.solved:
            return None  # a complete proof: accept as a lemma-free skeleton
        return ("No helper lemmas of the form `theorem name ... := by sorry` were found, and as a complete proof it fails:\n\n"
                + format_feedback(v.code, v))
    if len(sk.lemmas) == 1 and _conclusion(sk.lemmas[0][1]) == _conclusion(problem.statement):
            return ("This skeleton just restates the theorem as a single lemma and applies it; that is not a "
                    "decomposition. Split the proof into at least two genuinely smaller, separately provable steps "
                    "and do the combining work in the main proof.")
    for d in sk.context_decls:
        if re.search(r"\bsorry\b", re.sub(r"--[^\n]*", "", d)):
            return "Only helper lemma proofs (`theorem ... := by sorry`) may contain sorry; found sorry in:\n" + d[:500]
    code, _ = render(problem, sk.candidate)
    # sorry is expected; drop FORBIDDEN check for skeleton but compile it
    res = compile_lean(code)
    if not res.ok:
        from .problem import Verdict
        return "The skeleton does not compile:\n\n" + format_feedback(code, Verdict(False, res, code, "compile errors"))
    return None


def make_skeleton(problem: Problem, out_dir: Path, failures: str, rounds: int = 4, cancelled=None,
                  priority: int = 0, premises: str = "", plan: str = "") -> Skeleton | None:
    extra = ""
    if plan:
        extra += f"\nAn informal proof worked out earlier (use it if it is sound):\n{plan[-4000:]}\n"
    if premises:
        extra += f"\n{premises}\n"
    messages = [
        {"role": "system", "content": SKETCH_SYSTEM},
        {"role": "user", "content": SKETCH_PROMPT.format(header=problem.header, display=problem.display(),
                                                         failures=failures, extra=extra)},
    ]
    for rnd in range(rounds):
        if cancelled is not None and cancelled():
            return None
        try:
            resp = llm.chat_salvage(messages, max_tokens=16000, temperature=0.8, stop_check=cancelled, priority=priority,
                                   final_instruction="Output the informal proof briefly, then one ```lean block with defs, helper lemmas (`:= by sorry`) and the full main theorem.")
        except llm.LLMFailure:
            return None
        if resp.finish_reason == "cancelled":
            return None
        sk = prepare_skeleton(problem, resp.content)
        fb = "Output one ```lean block with the defs, helper lemmas (proved by sorry) and the full main theorem." if sk is None else validate_skeleton(problem, sk)
        with (out_dir / "skeletons.jsonl").open("a", encoding="utf-8") as fh:
            fh.write(json.dumps({"round": rnd, "ok": fb is None, "feedback": fb, "content": resp.content,
                                 "tokens": resp.completion_tokens}, ensure_ascii=False) + "\n")
        if fb is None:
            return sk
        messages.append({"role": "assistant", "content": resp.content[-8000:]})
        messages.append({"role": "user", "content": fb + "\n\nFix the skeleton and output it again in full."})
        if len(messages) > 8:
            messages = messages[:2] + messages[-6:]
    return None


def lemma_problem(problem: Problem, sk: Skeleton, name: str, stmt: str) -> Problem:
    ctx_parts = []
    has_sorry = False
    sol_txt = [sk.candidate.solutions.get(n, orig) for n, orig in problem.solution_defs]
    ctx_parts.extend(sol_txt)
    if problem.context:
        ctx_parts.append(problem.context)
        has_sorry = has_sorry or problem.context_has_sorry
    for kind, item in sk.order:
        if kind == "lemma" and item == name:
            break
        if kind == "decl":
            ctx_parts.append(item)
        else:
            other = dict(sk.lemmas)[item]
            ctx_parts.append(other + " by\n  sorry")
            has_sorry = True
    return Problem(name=name, header=problem.header, solution_defs=[], docstring="", statement=stmt,
                   context="\n\n".join(ctx_parts), context_has_sorry=has_sorry)


def falsify(problem: Problem) -> str | None:
    """Return a counterexample description if Lean's `plausible` refutes the statement, else None."""
    if problem.solution_defs:
        return None
    code, _ = render(problem, Candidate("", "  plausible", {}), check_axioms=False)
    res = compile_lean(code, timeout=60)
    for m in res.errors:
        if "Found a counter-example" in m.text:
            return m.text.strip()[:600]
    return None


def best_failed_attempt(dir_: Path) -> str:
    """Best (fewest errors) recorded attempt in a lemma directory, rendered for a re-sketch prompt."""
    from .history import error_count
    best = None
    try:
        for line in (dir_ / "attempts.jsonl").read_text(encoding="utf-8").splitlines():
            r = json.loads(line)
            if not r.get("code") or not r.get("feedback"):
                continue
            k = error_count(r["feedback"])
            if best is None or k < best[0]:
                best = (k, r)
    except OSError:
        return ""
    if best is None:
        return ""
    return "Main Lean errors of the best attempt at it:\n" + best[1]["feedback"][:1500]


def _alts(names: list[str]) -> str:
    return "  intros\n  first\n" + "\n".join(f"  | ({a}; done)" for a in names)


AUTO_BODIES = [
    _alts(["omega", "linarith", "positivity", "norm_num", "simp_all", "ring", "decide"]),
    _alts(["grind", "aesop", "(nlinarith [sq_nonneg (0:ℝ)])", "(field_simp; ring)", "(norm_num; ring_nf)",
           "(simp_all; ring_nf)", "(push_cast; ring)"]),
    "  intros\n  exact?",
]


def try_automation(problem: Problem) -> Candidate | None:
    """Deterministic tactics and library search before any model call."""
    if problem.solution_defs:
        return None
    with ThreadPoolExecutor(max_workers=len(AUTO_BODIES)) as ex:
        verdicts = list(ex.map(lambda b: check(problem, Candidate("", b, {})), AUTO_BODIES))
    for b, v in zip(AUTO_BODIES, verdicts):
        if not v.solved:
            continue
        if "exact?" not in b:
            return Candidate("", b, {})
        # substitute the suggestion so the stored proof does not re-run the search
        for m in v.result.messages:
            if m.severity == "information" and m.text.startswith("Try this:"):
                sug = m.text.split("\n", 1)[-1].strip().removeprefix("[apply]").strip()
                c = Candidate("", "  intros\n  " + sug, {})
                if check(problem, c).solved:
                    return c
        return Candidate("", b, {})
    return None


from .paths import LEMMA_CACHE
_cache_lock = threading.Lock()


def _cache_key(problem: Problem) -> str:
    import hashlib
    norm = lambda t: re.sub(r"\s+", " ", t).strip()
    return hashlib.sha256((norm(problem.context) + "\n#\n" + norm(problem.statement)).encode()).hexdigest()


def cache_lookup(problem: Problem) -> Candidate | None:
    key = _cache_key(problem)
    try:
        lines = LEMMA_CACHE.read_text(encoding="utf-8").splitlines()
    except OSError:
        return None
    for line in reversed(lines):
        row = json.loads(line)
        if row["key"] == key:
            cand = Candidate(row["helpers"], row["body"], {})
            if check(problem, cand).solved:
                return cand
    return None


def cache_store(problem: Problem, cand: Candidate) -> None:
    with _cache_lock, LEMMA_CACHE.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps({"key": _cache_key(problem), "name": problem.name, "helpers": cand.helpers,
                             "body": cand.body}, ensure_ascii=False) + "\n")


def solve(problem: Problem, out_dir: Path, depth: int, *, chains: int, rounds: int, max_depth: int,
          sketches: int, deadline: float, log=print, hint: str = "",
          cancels: tuple = (), seed_skeletons: list | None = None, root: dict | None = None) -> Candidate | None:
    root = root if root is not None else {"calls": 0, "name": problem.name}
    from .agent import runtime_config
    cfg = runtime_config()
    out_dir.mkdir(parents=True, exist_ok=True)
    import dataclasses
    (out_dir / "problem.json").write_text(json.dumps(dataclasses.asdict(problem), ensure_ascii=False), encoding="utf-8")
    state = ProblemState(problem, out_dir)
    my_cancel = threading.Event()
    cancels = tuple(cancels) + (my_cancel,)

    def cancelled() -> bool:
        return time.time() > deadline or any(e.is_set() for e in cancels)

    if cancelled():
        return None
    if depth > 0 and cfg.get("lemma_cache", True):
        cached = cache_lookup(problem)
        if cached is not None:
            log(f"[depth {depth}] {problem.name}: solved from lemma cache")
            return cached
        cex = falsify(problem)
        if cex is not None:
            log(f"[depth {depth}] {problem.name}: FALSE (plausible counterexample)")
            (out_dir / "falsified.txt").write_text(cex, encoding="utf-8")
            return None
    auto = try_automation(problem)
    if auto is not None:
        log(f"[depth {depth}] {problem.name}: solved by automation")
        return auto

    result: list[Candidate] = []
    result_lock = threading.Lock()

    def finish(c: Candidate) -> None:
        with result_lock:
            if not result:
                result.append(c)
        my_cancel.set()

    direct_done = threading.Event()

    def direct() -> None:
        try:
            _direct()
        finally:
            direct_done.set()

    def _direct() -> None:
        with ThreadPoolExecutor(max_workers=chains) as ex:
            list(ex.map(lambda c: run_chain(state, c, rounds, hint=hint, deadline=deadline, cancelled=cancelled,
                                                   priority=int(cfg.get("depth_weight", 2)) * depth,
                                                   stall_rounds=(stall if depth < max_depth else 0),
                                                   depth=depth, root=root),
                        range(chains)))
        if state.solved and state.solved_candidate is not None:
            log(f"[depth {depth}] {problem.name}: solved directly")
            finish(state.solved_candidate)

    from .agent import runtime_config
    cfg = runtime_config()
    stall = int(cfg.get("stall_rounds", 2) or 0)
    n_workers = int(cfg.get("parallel_sketches", 2)) if depth == 0 else 1
    seeds_lock = threading.Lock()
    failures_box = [""]
    next_index = [0]

    def decomposition() -> None:
        with ThreadPoolExecutor(max_workers=n_workers) as ex:
            list(ex.map(lambda w: decomposition_worker(), range(n_workers)))

    def decomposition_worker() -> None:
        while True:
            if cancelled():
                return
            with state.lock:
                has_harvest = bool(state.harvested)
            with seeds_lock:
                if next_index[0] >= sketches and not has_harvest:
                    s = None
                else:
                    s = next_index[0]
                    next_index[0] += 1
            if s is None:
                if direct_done.is_set():
                    return
                time.sleep(5)  # the direct attempts may still produce a sorry-gapped proof to harvest
                continue
            with seeds_lock:
                failures_box[0] = failures_box[0] or _failure_summary(state)
                failures = failures_box[0]
            sk_dir = out_dir / f"sketch_{s}"
            sk_dir.mkdir(exist_ok=True)
            sk = None
            with state.lock:
                pending = state.harvested.pop() if state.harvested else None
            if pending is not None:
                hskel, hlemmas, horder = pending
                sk = Skeleton(hskel, [t for k, t in horder if k == "decl"], hlemmas, horder, "")
                log(f"[depth {depth}] {problem.name}: using harvested sorry-skeleton")
            while sk is None:
                with seeds_lock:
                    raw = seed_skeletons.pop(0) if seed_skeletons else None
                if raw is None:
                    break
                cand_sk = prepare_skeleton(problem, raw)
                if cand_sk is not None and validate_skeleton(problem, cand_sk) is None:
                    sk = cand_sk
                    log(f"[depth {depth}] {problem.name}: resumed skeleton from a previous run")
                    with (sk_dir / "skeletons.jsonl").open("a", encoding="utf-8") as fh:
                        fh.write(json.dumps({"round": "resumed", "ok": True, "feedback": None, "content": raw},
                                            ensure_ascii=False) + "\n")
            if sk is None:
                from .agent import ensure_prep
                ensure_prep(state, hint, int(cfg.get("depth_weight", 2)) * depth - root["calls"], cancelled, depth=depth)  # waits for (or computes) search results + plan
                root["calls"] += 1
                sk = make_skeleton(problem, sk_dir, failures, cancelled=cancelled,
                                   priority=int(cfg.get("depth_weight", 2)) * depth + 1 - root["calls"] // int(cfg.get("fair_share_calls", 1)),
                                   premises=state.premises or "", plan=state.plan or "")
            if sk is None:
                log(f"[depth {depth}] {problem.name}: sketch {s} invalid")
                continue
            if not sk.lemmas:
                v = check(problem, sk.candidate)
                if v.solved:  # the "skeleton" was already a complete proof
                    log(f"[depth {depth}] {problem.name}: solved via sketch {s} (complete proof)")
                    (out_dir / "proof.lean").write_text(v.code, encoding="utf-8")
                    finish(sk.candidate)
                    return
                continue
            log(f"[depth {depth}] {problem.name}: sketch {s} with lemmas {[n for n, _ in sk.lemmas]}")
            subs = [(n, lemma_problem(problem, sk, n, st)) for n, st in sk.lemmas]
            sketch_cancel = threading.Event()
            failed: list[str] = []

            def sub(item):
                r = solve(item[1], sk_dir / item[0], depth + 1, chains=max(1, chains - 1), rounds=rounds,
                          max_depth=max_depth, sketches=max(1, sketches - 1), deadline=deadline, log=log,
                          hint="Overall informal proof this lemma is part of:\n" + sk.prose[-2500:],
                          cancels=cancels + (sketch_cancel,), root=root)
                if r is None:
                    failed.append(item[0])
                    sketch_cancel.set()  # one lemma failed: abandon this sketch
                return r

            with ThreadPoolExecutor(max_workers=len(subs)) as ex:
                results = list(ex.map(sub, subs))
            if cancelled():
                return
            if failed or any(r is None for r in results):
                log(f"[depth {depth}] {problem.name}: sketch {s} failed lemmas {failed}")
                parts = []
                for n in failed[:2]:
                    ldir = sk_dir / n
                    why = ""
                    if (ldir / "falsified.txt").exists():
                        why = "It is FALSE; Lean's `plausible` found a counterexample:\n" + \
                            (ldir / "falsified.txt").read_text(encoding="utf-8")
                    else:
                        why = best_failed_attempt(ldir)
                    parts.append(dict(sk.lemmas)[n] + "\n" + why)
                with seeds_lock:
                    failures_box[0] += ("\nA previous skeleton failed at this lemma (it is false or was too hard to "
                                        "formalize); choose a different decomposition that avoids it or splits it "
                                        "into smaller, clearly true steps:\n" + "\n---\n".join(parts)[:4000] + "\n")
                continue
            proved = {n: r for (n, _), r in zip(subs, results)}
            helpers = []
            for kind, item in sk.order:
                if kind == "decl":
                    helpers.append(item)
                else:
                    r = proved[item]
                    if r.helpers:
                        helpers.append(r.helpers)
                    helpers.append(dict(sk.lemmas)[item] + " by\n" + r.body)
            final = Candidate("\n\n".join(helpers), sk.candidate.body, dict(sk.candidate.solutions))
            v = check(problem, final)
            with (sk_dir / "assembly.json").open("w", encoding="utf-8") as fh:
                json.dump({"solved": v.solved, "reason": v.reason, "code": v.code,
                           "errors": [m.text for m in v.result.errors]}, fh, ensure_ascii=False, indent=2)
            if v.solved:
                log(f"[depth {depth}] {problem.name}: solved via sketch {s}")
                (out_dir / "proof.lean").write_text(v.code, encoding="utf-8")
                finish(final)
                return
            log(f"[depth {depth}] {problem.name}: assembly failed: {v.reason} {[m.text[:200] for m in v.result.errors[:2]]}")

    if depth == 0 and depth < max_depth and (cfg.get("race_top", True) or seed_skeletons):
        # top level: direct attempts and decomposition race each other
        threads = [threading.Thread(target=direct), threading.Thread(target=decomposition)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
    else:
        direct()
        if not result and depth < max_depth and not cancelled():
            decomposition()
    if not result:
        log(f"[depth {depth}] {problem.name}: failed")
    elif depth > 0:
        cache_store(problem, result[0])
    return result[0] if result else None


def _failure_summary(state: ProblemState) -> str:
    fails = [a for a in state.attempts if a.feedback][-3:]
    if not fails:
        return ""
    txt = "\nRecent errors from direct attempts (for information):\n" + "\n---\n".join(a.feedback[:1200] for a in fails)
    return txt + "\n"
