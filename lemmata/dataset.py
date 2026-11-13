"""Export proof runs as structured SFT, Reasoning-SFT, DPO, and multi-turn Agent RL datasets.

Examples:
    python3 -m lemmata.dataset runs/web_20261113_011614_b6fe -o dataset.jsonl
    python3 -m lemmata.dataset runs/ -o sft.jsonl --kinds prove_sft,sketch_sft,repair_sft --tree-solved-only
    python3 -m lemmata.dataset runs/ -o dpo.jsonl --kinds repair_dpo
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from .agent import SYSTEM, initial_prompt
from .decompose import CODE_BLOCK_STRIP, SKETCH_PROMPT, SKETCH_SYSTEM, parse_skeleton
from .paths import RUNS_DIR
from .problem import Problem, candidate_block, prune_unused, split_full_code

ALL_KINDS = ("prove_sft", "sketch_sft", "repair_sft", "repair_dpo", "agent_trajectory", "raw_llm_call")


def _assistant_msg(answer: str, reasoning: str = "", *, think_tags: bool = True) -> dict:
    reasoning = (reasoning or "").strip()
    answer = (answer or "").strip()
    if reasoning and think_tags:
        content = f"<think>\n{reasoning}\n</think>\n\n{answer}" if answer else f"<think>\n{reasoning}\n</think>"
    else:
        content = answer
    msg: dict = {"role": "assistant", "content": content}
    if reasoning:
        msg["reasoning_content"] = reasoning
    return msg


def _recover_clean_block(problem: Problem, row: dict) -> str:
    if row.get("clean_block"):
        return row["clean_block"]
    code = row.get("code") or ""
    if code:
        body_part = code.split("#print axioms")[0]
        cand = split_full_code(problem, body_part)
        if cand is not None:
            return candidate_block(problem, prune_unused(cand))
    return ""


def _default_prove_messages(node_dir: Path, problem: Problem) -> list[dict]:
    premises = ""
    prem_file = node_dir / "premises.txt"
    if prem_file.exists():
        txt = prem_file.read_text(encoding="utf-8")
        parts = txt.split("\n\n", 1)
        premises = parts[1] if len(parts) > 1 else ""
    plan = (node_dir / "plan.md").read_text(encoding="utf-8") if (node_dir / "plan.md").exists() else ""
    return [
        {"role": "system", "content": SYSTEM},
        {"role": "user", "content": initial_prompt(problem, premises=premises, plan=plan)},
    ]


def _default_sketch_messages(node_dir: Path, problem: Problem) -> list[dict]:
    extra = ""
    if problem.context:
        extra += ("\nAll declarations shown above the target theorem are ALREADY available in the file; "
                  f"use them freely in your proof of `{problem.name}`, and do NOT repeat or re-state them. "
                  f"Decompose ONLY the target theorem `{problem.name}`.\n")
    prem_file = node_dir / "premises.txt"
    if prem_file.exists():
        parts = prem_file.read_text(encoding="utf-8").split("\n\n", 1)
        if len(parts) > 1 and parts[1].strip():
            extra += f"\n{parts[1]}\n"
    return [
        {"role": "system", "content": SKETCH_SYSTEM},
        {"role": "user", "content": SKETCH_PROMPT.format(header=problem.header, display=problem.display(),
                                                         failures="", extra=extra)},
    ]


def _depth_of(rel: str) -> int:
    return rel.count("sketch_")


def export_run(run_dir: Path, *, kinds: set[str] | None = None, think_tags: bool = True,
               tree_solved_only: bool = False, include_resumed: bool = False) -> list[dict]:
    """Extract structured training records from a single campaign/web run directory."""
    want = set(ALL_KINDS) if kinds is None else set(kinds)
    records: list[dict] = []
    run_id = run_dir.name
    seen_keys: set[tuple[str, str, str]] = set()

    def emit(rec: dict, dedup_sig: str) -> None:
        k = (rec["kind"], rec.get("problem", ""), dedup_sig)
        if k not in seen_keys:
            seen_keys.add(k)
            records.append(rec)

    for pj in sorted(run_dir.rglob("problem.json")):
        node_dir = pj.parent
        try:
            problem = Problem(**json.loads(pj.read_text(encoding="utf-8")))
        except Exception:
            continue
        rel_node = str(node_dir.relative_to(run_dir))
        depth = _depth_of(rel_node)
        node_solved = (node_dir / "proof.lean").exists()

        # 1. Direct proof attempts, repairs, DPO pairs, and multi-turn trajectories
        att_file = node_dir / "attempts.jsonl"
        if att_file.exists():
            rows = []
            for line in att_file.read_text(encoding="utf-8").splitlines():
                try:
                    rows.append(json.loads(line))
                except ValueError:
                    continue
            base_msgs = _default_prove_messages(node_dir, problem)
            wins = [r for r in rows if r.get("solved")]
            fails = [r for r in rows if not r.get("solved") and r.get("code") and r.get("feedback")]

            for w in wins:
                cblock = _recover_clean_block(problem, w)
                if not cblock:
                    continue
                vreason = w.get("verdict_reason") or ""
                is_repair = vreason.startswith("repair")
                reasoning = w.get("reasoning") or ""
                prose = ""
                if not is_repair and w.get("raw"):
                    prose = CODE_BLOCK_STRIP.sub("", w["raw"]).strip()
                ans_text = ((prose + "\n\n") if prose else "") + f"```lean4\n{cblock}\n```"
                w_msgs = w.get("messages") or base_msgs

                if "prove_sft" in want:
                    if not is_repair:
                        asst = _assistant_msg(ans_text, reasoning, think_tags=think_tags)
                        emit({
                            "kind": "prove_sft",
                            "run_id": run_id,
                            "node": rel_node,
                            "problem": problem.name,
                            "depth": depth,
                            "mode": vreason.split(":")[0],
                            "patched": bool(w.get("patched")),
                            "has_reasoning": bool(reasoning),
                            "messages": list(w_msgs) + [asst],
                        }, cblock)
                    else:
                        # Also provide a clean single-turn (statement -> verified proof) sample
                        asst_direct = _assistant_msg(f"```lean4\n{cblock}\n```", "", think_tags=think_tags)
                        emit({
                            "kind": "prove_sft",
                            "run_id": run_id,
                            "node": rel_node,
                            "problem": problem.name,
                            "depth": depth,
                            "mode": vreason.split(":")[0] + "_distilled",
                            "patched": bool(w.get("patched")),
                            "has_reasoning": False,
                            "messages": list(base_msgs) + [asst_direct],
                        }, "distilled:" + cblock)

                if is_repair and "repair_sft" in want and w.get("messages"):
                    asst_rep = _assistant_msg(f"```lean4\n{cblock}\n```", reasoning, think_tags=think_tags)
                    emit({
                        "kind": "repair_sft",
                        "run_id": run_id,
                        "node": rel_node,
                        "problem": problem.name,
                        "depth": depth,
                        "mode": vreason.split(":")[0],
                        "patched": bool(w.get("patched")),
                        "has_reasoning": bool(reasoning),
                        "messages": list(w["messages"]) + [asst_rep],
                    }, "repair:" + cblock)

                # Multi-turn environment trajectory for this chain up to the winning attempt
                if "agent_trajectory" in want:
                    asst_reasoning: dict[str, str] = {}
                    tc_file = node_dir / "llm_calls.jsonl"
                    if tc_file.exists():
                        for tline in tc_file.read_text(encoding="utf-8").splitlines():
                            try:
                                tr = json.loads(tline)
                            except ValueError:
                                continue
                            if tr.get("chain") == w.get("chain") and tr.get("reasoning") and tr.get("content"):
                                asst_reasoning[tr["content"].strip()] = tr["reasoning"]
                    chain_rows = [r for r in rows if r.get("chain") == w.get("chain") and r.get("round", 0) <= w.get("round", 0)]
                    for r in chain_rows:
                        if r.get("reasoning"):
                            if r.get("raw"):
                                asst_reasoning[r["raw"].strip()] = r["reasoning"]
                            if r.get("model_code"):
                                asst_reasoning[f"```lean\n{r['model_code'].strip()}\n```"] = r["reasoning"]
                            rb0 = _recover_clean_block(problem, r)
                            if rb0:
                                asst_reasoning[f"```lean\n{rb0.strip()}\n```"] = r["reasoning"]

                    if w.get("messages"):
                        # Exact conversation history recorded at inference time (immune to parallel n>1 sibling samples)
                        traj = []
                        for m in w["messages"]:
                            if m.get("role") == "assistant":
                                mc = (m.get("content") or "").strip()
                                sr = m.get("reasoning_content") or asst_reasoning.get(mc, "")
                                traj.append(_assistant_msg(mc, sr, think_tags=think_tags))
                            else:
                                traj.append({"role": m.get("role", ""), "content": m.get("content", "")})
                        traj.append(_assistant_msg(ans_text, reasoning, think_tags=think_tags))
                    else:
                        # Legacy run fallback (before `messages` were persisted on Attempt)
                        traj = list(base_msgs)
                        seen_stages: set[tuple] = set()
                        for r in chain_rows:
                            if r is w:
                                traj.append(_assistant_msg(ans_text, reasoning, think_tags=think_tags))
                                break
                            stage_key = (r.get("round"), str(r.get("verdict_reason", "")).split(":")[0])
                            if stage_key in seen_stages:
                                continue
                            rb = _recover_clean_block(problem, r)
                            if not rb or not r.get("feedback"):
                                continue
                            seen_stages.add(stage_key)
                            r_prose = CODE_BLOCK_STRIP.sub("", r.get("raw") or "").strip() if str(r.get("verdict_reason", "")).startswith("think") else ""
                            r_ans = ((r_prose + "\n\n") if r_prose else "") + f"```lean4\n{rb}\n```"
                            traj.append(_assistant_msg(r_ans, r.get("reasoning") or "", think_tags=think_tags))
                            traj.append({
                                "role": "user",
                                "content": ("Lean rejected this attempt. Compiler output:\n\n" + r["feedback"] +
                                            "\n\nFix the proof and output the complete corrected code in one ```lean block."),
                            })
                    if len(traj) > 3:
                        emit({
                            "kind": "agent_trajectory",
                            "run_id": run_id,
                            "node": rel_node,
                            "problem": problem.name,
                            "depth": depth,
                            "turns": (len(traj) - 1) // 2,
                            "has_reasoning": any("reasoning_content" in m for m in traj if m["role"] == "assistant"),
                            "messages": traj,
                        }, "traj:" + cblock)

            if wins and fails and "repair_dpo" in want:
                w0 = wins[0]
                cb_win = _recover_clean_block(problem, w0)
                if cb_win:
                    # Prefer same-prompt sibling failures when `messages` match; else pair on `base_msgs`
                    w_msgs = w0.get("messages") or []
                    same_prompt_fails = [f for f in fails if w_msgs and f.get("messages") == w_msgs]
                    target_fails = same_prompt_fails or fails[-2:]
                    prompt_msgs = w_msgs if same_prompt_fails else base_msgs
                    w_matches_prompt = bool(same_prompt_fails) or (
                        (w0.get("messages") or base_msgs) == prompt_msgs
                        and not str(w0.get("verdict_reason", "")).startswith("repair")
                    )
                    chosen_msg = _assistant_msg(f"```lean4\n{cb_win}\n```",
                                                (w0.get("reasoning") or "") if w_matches_prompt else "",
                                                think_tags=think_tags)
                    for f in target_fails[:2]:
                        cb_fail = _recover_clean_block(problem, f)
                        if not cb_fail or cb_fail == cb_win:
                            continue
                        f_matches_prompt = bool(same_prompt_fails) or (
                            (f.get("messages") or base_msgs) == prompt_msgs
                            and not str(f.get("verdict_reason", "")).startswith("repair")
                        )
                        rej_msg = _assistant_msg(f"```lean4\n{cb_fail}\n```",
                                                 (f.get("reasoning") or "") if f_matches_prompt else "",
                                                 think_tags=think_tags)
                        emit({
                            "kind": "repair_dpo",
                            "run_id": run_id,
                            "node": rel_node,
                            "problem": problem.name,
                            "depth": depth,
                            "same_prompt": bool(same_prompt_fails),
                            "prompt": prompt_msgs,
                            "chosen": chosen_msg,
                            "rejected": rej_msg,
                            "rejected_feedback": (f.get("feedback") or "")[:2000],
                        }, cb_win + "||" + cb_fail)

        # 2. Decomposition skeletons
        if "sketch_sft" in want:
            for sj in sorted(node_dir.glob("sketch_*/skeletons.jsonl")):
                sk_dir = sj.parent
                asm_file = sk_dir / "assembly.json"
                asm_solved = False
                if asm_file.exists():
                    try:
                        asm_solved = bool(json.loads(asm_file.read_text(encoding="utf-8")).get("solved"))
                    except Exception:
                        asm_solved = False
                tree_ok = asm_solved or (node_solved and any(sk_dir.glob("*/proof.lean")))
                if tree_solved_only and not tree_ok:
                    continue
                for line in sj.read_text(encoding="utf-8").splitlines():
                    try:
                        srow = json.loads(line)
                    except ValueError:
                        continue
                    if not srow.get("ok"):
                        continue
                    rnd_tag = srow.get("round")
                    if rnd_tag in ("resumed", "harvested") and not include_resumed:
                        continue
                    raw_c = srow.get("content") or ""
                    sk = parse_skeleton(problem, raw_c)
                    if sk is None:
                        continue
                    cblock = srow.get("clean_block") or candidate_block(problem, sk.candidate)
                    prose = CODE_BLOCK_STRIP.sub("", raw_c).strip()
                    ans_text = ((prose + "\n\n") if prose else "") + f"```lean4\n{cblock}\n```"
                    reasoning = srow.get("reasoning") or ""
                    s_msgs = srow.get("messages") or _default_sketch_messages(node_dir, problem)
                    emit({
                        "kind": "sketch_sft",
                        "run_id": run_id,
                        "node": str(sk_dir.relative_to(run_dir)),
                        "problem": problem.name,
                        "depth": depth,
                        "tree_solved": tree_ok,
                        "lemmas": [n for n, _ in sk.lemmas],
                        "has_reasoning": bool(reasoning),
                        "messages": list(s_msgs) + [_assistant_msg(ans_text, reasoning, think_tags=think_tags)],
                    }, cblock)

        # 3. Raw lossless LLM call trace (includes query_gen, plan, think, salvage, sketch, repair)
        if "raw_llm_call" in want:
            for trace_file in [node_dir / "llm_calls.jsonl", *sorted(node_dir.glob("sketch_*/llm_calls.jsonl"))]:
                if not trace_file.exists():
                    continue
                for line in trace_file.read_text(encoding="utf-8").splitlines():
                    try:
                        trow = json.loads(line)
                    except ValueError:
                        continue
                    rec = {"kind": "raw_llm_call", "run_id": run_id, "node": str(trace_file.parent.relative_to(run_dir))}
                    rec.update(trow)
                    records.append(rec)

    return records


def export_jsonl_bytes(run_dir: Path, **kw) -> bytes:
    rows = export_run(run_dir, **kw)
    return "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows).encode("utf-8")


def _discover_runs(paths: list[str]) -> list[Path]:
    if not paths:
        paths = [str(RUNS_DIR)]
    out: list[Path] = []
    for raw in paths:
        p = Path(raw)
        if not p.exists():
            continue
        if (p / "summary.json").exists() or (p / "job.json").exists() or any(p.glob("*/problem.json")):
            out.append(p)
        else:
            for sub in sorted(p.iterdir()):
                if sub.is_dir() and ((sub / "summary.json").exists() or (sub / "job.json").exists()):
                    out.append(sub)
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description="Export Lemmata proof runs into SFT / Reasoning / DPO / RL JSONL datasets.")
    ap.add_argument("paths", nargs="*", help="run directory or parent `runs/` directory (default: runs/)")
    ap.add_argument("-o", "--output", default="-", help="output .jsonl path, or '-' for stdout")
    ap.add_argument("--kinds", default="prove_sft,sketch_sft,repair_sft,repair_dpo,agent_trajectory",
                    help=f"comma-separated record kinds from {','.join(ALL_KINDS)}, or 'all'")
    ap.add_argument("--no-think-tags", action="store_true",
                    help="keep `<think>` out of assistant `content` (still stored in `reasoning_content`)")
    ap.add_argument("--tree-solved-only", action="store_true",
                    help="for `sketch_sft`, keep only skeletons whose sub-tree produced a complete proof")
    ap.add_argument("--include-resumed", action="store_true",
                    help="include resumed/harvested skeletons in `sketch_sft`")
    args = ap.parse_args()

    kinds = set(ALL_KINDS) if args.kinds.strip() == "all" else {k.strip() for k in args.kinds.split(",") if k.strip()}
    unknown = kinds - set(ALL_KINDS)
    if unknown:
        ap.error(f"unknown kinds: {sorted(unknown)}; choose from {ALL_KINDS}")

    runs = _discover_runs(args.paths)
    all_rows: list[dict] = []
    counts: dict[str, int] = {}
    with_reasoning = 0
    for rdir in runs:
        rows = export_run(rdir, kinds=kinds, think_tags=not args.no_think_tags,
                          tree_solved_only=args.tree_solved_only, include_resumed=args.include_resumed)
        for r in rows:
            counts[r["kind"]] = counts.get(r["kind"], 0) + 1
            if r.get("has_reasoning") or r.get("reasoning"):
                with_reasoning += 1
        all_rows.extend(rows)

    payload = "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in all_rows)
    if args.output == "-":
        sys.stdout.write(payload)
    else:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(payload, encoding="utf-8")
        print(f"Exported {len(all_rows)} records from {len(runs)} run(s) -> {out_path} "
              f"(with_reasoning={with_reasoning}, by_kind={counts})", file=sys.stderr)


if __name__ == "__main__":
    main()
