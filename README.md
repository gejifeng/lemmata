# lean_prover

A small LLM agent that proves competition mathematics in **Lean 4 + Mathlib**, with the Lean compiler as the only
judge. It was built to run on a single locally served open-weight model and is evaluated on
[PutnamBench](https://github.com/trishullab/PutnamBench).

[中文说明](README.zh-CN.md)

## Results

All proofs listed here are in [`results/proofs/`](results/proofs). Each one was re-checked from scratch with
`python -m lean_prover.report`:

- the theorem statement is identical to PutnamBench;
- the proof contains no `sorry`;
- the proof depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

| Problem set | Verified |
|---|---|
| Main set: 13 PutnamBench problems used during development | **6 / 13** |
| Easy set: 20 additional, mostly elementary PutnamBench problems | **19 / 20** |
| **Total** | **25 / 33** |

Setup for all experiments:

- **Model:** one open-weight model (`qwen3.8-flash-next`) served locally by vLLM, used with thinking enabled.
- **Throughput:** at most 8 concurrent requests, about 90 output tokens/s in aggregate, about 12 tokens/s per request.
- **Lean:** v4.28.0 with Mathlib v4.28.0.
- **Cost:** the experiments below generated about 21 million tokens in total.

Some problems were solved in one run and others in later runs that reused proved lemmas and earlier attempts.
The single-run comparison is in the next section.

<details>
<summary>Per-problem results</summary>

| Problem | Domain | Status |
|---|---|---|
| putnam_2001_a1 | algebra (binary operation) | ✅ (automation layer, no model call) |
| putnam_1992_a1 | functional equation | ✅ |
| putnam_1993_a2 | recurrence | ✅ |
| putnam_1966_a1 | sums, integer division | ✅ (3-lemma decomposition) |
| putnam_1963_a2 | multiplicative function | ✅ (5-lemma decomposition) |
| putnam_1965_b5 | graph theory (triangle-free graphs) | ✅ (7-lemma decomposition, proved over 4 runs) |
| putnam_1999_a2 | real polynomials, sums of squares | ❌ 6/7 lemmas; stuck on the factorization lemma |
| putnam_1969_a2 | determinants | ❌ |
| putnam_2000_a4 | improper integrals | ❌ |
| putnam_1962_a1 | plane geometry (convex position) | ❌ |
| putnam_1964_a1 | plane geometry (distances) | ❌ needs Jung's theorem, which is not in Mathlib |
| putnam_1965_a1 | plane geometry (angles) | ❌ |
| putnam_1976_b3 | probability | ❌ |
| easy set (20 problems) | number theory, algebra, combinatorics, analysis | ✅ 19, ❌ putnam_2001_a5 |

</details>

### What mattered: same 20 problems, same 6 hours, same model

| Run | Strategy | Solved | Generated tokens | Tokens per solved problem |
|---|---|---|---|---|
| e1 (baseline) | direct attempts racing one decomposition | 8 / 20 | 1.71 M | ~213 k |
| e2 | + Mathlib search, deterministic repair, informal plan, 2 parallel skeletons | 7 / 20 | 1.74 M | ~249 k |
| e3 | e2 + strictly fair scheduling | 4 / 20 | 1.70 M | ~424 k |
| **e4** | **cheap first, decompose only on stall** (current default) | **13 / 20** | 1.92 M | **~148 k** |

What these runs showed:

1. **Scheduling mattered most.**
   - At this throughput, writing an informal plan and parallel skeletons up front costs more than it returns. e3 made only 39 proof attempts in 6 hours.
   - The default is now: try cheap things first, and decompose only when progress stalls.
2. **Retrieval and deterministic repair reduce wasted rounds.**
   - Failed attempts containing an unknown Mathlib name fell from 32% to 15%.
   - Attempts that ran out of output budget fell from 5 to 0.
3. **Decomposition plus a lemma cache let hard problems make progress across runs.** The 7 lemmas of putnam_1965_b5 were proved over four runs.
4. **The remaining hard problems are limited by the model, not the framework.** Each is blocked on one core step that needs a 60–200-line technical proof:
   - In 50–130 attempts per step, the error count stopped improving.
   - The model often left the hardest step as `sorry`.
   - It could not split the step further.
   - Unknown names cause only about 9% of these failures on their own.

## How it works

```
problem ──▶ automation ──▶ direct attempts ──stall──▶ decomposition ──▶ each lemma: same pipeline (recursive)
            (no model)     think → compile →         skeleton with       (depth ≤ 3; lemma cache;
                           cheap repairs             `sorry` lemmas      false lemmas rejected early)
```

- **Lean is the only judge.**
  - The theorem statement is fixed by construction.
  - A candidate is accepted only if it compiles with no `sorry` and `#print axioms` shows only the standard axioms.
  - Everything else (informal proofs, skeletons, search results) is advisory and can never abort a run.
- **Automation layer** (`decompose.try_automation`), before any model call:
  - `omega`, `linarith`, `positivity`, `norm_num`, `simp_all`, `ring`, `decide`, `grind`, `aesop`, `nlinarith`, `field_simp`;
  - `exact?` (Mathlib library search), whose suggestion is substituted into the proof.
- **Direct attempts** (`agent.run_chain`):
  - A thinking attempt writes a complete proof.
  - Lean's errors go back to the model. Unknown names come back with real Mathlib names and their types, taken from a local index of 450k declarations.
  - Up to 4 cheap non-thinking repair requests follow, each sampling 2 candidates.
  - If the thinking budget runs out, a non-thinking follow-up turns the partial reasoning into code.
- **Deterministic repair, no model tokens** (`autopatch.py`):
  - failing `have` steps are replaced by an automation combo ending in `exact?`;
  - tactics reported as "No goals to be solved" are deleted.
- **Mathlib search** (`search.py`):
  - [LeanSearch](https://leansearch.net) for natural-language queries, [Loogle](https://loogle.lean-lang.org) for constant/type patterns.
  - Every result is checked against the local Mathlib, because the services index newer versions.
  - Search is used before the first attempt, through ```` ```search ```` blocks the model can write, and on unknown-name errors.
- **Decomposition** (`decompose.py`):
  - The model writes a Lean skeleton with helper lemmas proved by `sorry`.
  - It must compile; restatements of the theorem are rejected.
  - Each lemma is solved recursively.
  - Lemmas are checked for counterexamples with `plausible` first; a false lemma abandons the skeleton and is reported back for the next one.
  - A direct attempt that compiles except for `sorry` gaps is turned into a skeleton automatically (`harvest.py`): each gap's exact goal comes from `extract_goal`.
- **Scheduling** (`llm.py`, `agent.py`):
  - A priority queue over model requests.
  - Priority goes down as a problem uses more calls (fair share) and when it stalls; sub-lemmas get a small bonus.
- **Persistence across runs:**
  - proved lemmas are cached by statement;
  - a new run starts from the best earlier attempt on the same statement (`history.py`);
  - valid skeletons can be reused (`--resume-from`).

## Setup

Requirements:

- Linux;
- Python ≥ 3.10 (standard library only, no dependencies);
- `git` and `curl`;
- about 10 GB of disk for Mathlib;
- an OpenAI-compatible chat endpoint.

Thinking is switched on and off with vLLM's `chat_template_kwargs.enable_thinking` (Qwen-style chat templates).
Other servers may ignore this field.

```bash
git clone <this repo> lean_prover && cd lean_prover
./scripts/setup.sh          # elan + Lean, Mathlib cache, PutnamBench, Mathlib name index (~30 min)

export LEAN_PROVER_BASE_URL=http://localhost:8000/v1   # OpenAI-compatible endpoint
export LEAN_PROVER_MODEL=<served model name>
export LEAN_PROVER_API_KEY=...                          # optional
```

## Usage

```bash
# prove problems (outputs in runs/<run>/; FINAL_proof.lean for each solved problem)
python -m lean_prover.campaign --set easy --hours 6 --run my_run
python -m lean_prover.campaign putnam_1977_a5 putnam_1988_b1 --hours 1

# continue hard problems, reusing skeletons from earlier runs (lemma cache and best attempts are reused automatically)
python -m lean_prover.campaign --set main --hours 12 --run my_run2 --resume-from my_run

# re-verify all solved problems from scratch and collect them into results/proofs/
python -m lean_prover.report all

# per-run statistics: solved problems, tokens per problem, error categories
python -m lean_prover.metrics my_run

# offline end-to-end self-test (scripted fake model, real Lean; no model calls)
python -m lean_prover.selftest
```

Search settings are in [`config/default.json`](config/default.json). The file is re-read on every use, so it can
be edited while a campaign runs. The main knobs:

| Key | Default | Meaning |
|---|---|---|
| `stall_rounds` | 2 | thinking rounds without fewer compiler errors before decomposing |
| `race_top` | false | decompose in parallel with direct attempts from the start (always on when `--resume-from` provides a skeleton) |
| `quick_repairs` / `repair_samples` | 4 / 2 | non-thinking repair requests after each thinking attempt, and samples per request |
| `think_max_tokens` | 14000 | output budget of a thinking attempt |
| `search` | true | Mathlib retrieval |
| `two_stage` | false | write an informal plan before formalizing (made things worse at our throughput) |
| `fair_share_calls` | 3 | priority drops by 1 for every N model calls a problem has used |
| `resume_previous` / `lemma_cache` | true / true | reuse attempts and lemmas from earlier runs |

Environment variables:

| Variable | Default | Meaning |
|---|---|---|
| `LEAN_PROVER_LLM_JOBS` | 6 | concurrent thinking requests |
| `LEAN_PROVER_QUICK_JOBS` | 2 | concurrent non-thinking requests |
| `LEAN_PROVER_COMPILE_JOBS` | 10 | concurrent Lean compilations |
| `PUTNAMBENCH_DIR` | `benchmarks/PutnamBench/lean4/src` | PutnamBench sources |
| `LEAN_PROVER_RUNS_DIR` | `runs/` | campaign output directory |
| `LEAN_PROVER_WORK_DIR` | `.work/` | scratch files, caches, name index |
| `LEAN_PROVER_CONFIG` | `config/default.json` | search settings file |

## Repository layout

```
lean_prover/
  campaign.py    command line: run a set of problems in parallel
  decompose.py   solve(): automation → direct attempts → decomposition (recursive), lemma cache, falsity check
  agent.py       direct proof chains, prompts, feedback, runtime config
  problem.py     PutnamBench parsing, candidate extraction, rendering and the acceptance check
  lean.py        `lake env lean --json` wrapper, axiom check, compile cache
  llm.py         streaming OpenAI-compatible client, priority scheduling, thinking-budget salvage
  search.py      LeanSearch / Loogle retrieval checked against the local Mathlib
  names.py       real-name suggestions for unknown identifiers
  autopatch.py   deterministic repairs (automation combo + exact?, dead-tactic removal)
  harvest.py     turn `sorry` gaps into lemmas via `extract_goal`
  history.py     best earlier attempt per statement
  report.py      independent re-verification of all proofs
  metrics.py     run statistics
  selftest.py    offline end-to-end test
  benchmarks.py  problem sets
config/default.json   search settings
scripts/              setup and the Mathlib name-index generator
results/proofs/       the 25 verified proofs
```

## Limitations

- Throughput-bound: with about 90 tokens/s, a thinking attempt takes 20–30 minutes, so hard steps get only
  tens to a hundred attempts. Systems that solve such problems typically use RL-trained provers with far more samples.
- Geometry and measure-theoretic probability are the weakest areas.
- Answer-type problems (with a `solution` definition) are supported, but the answer itself is checked only by
  the proof, as in PutnamBench.
- Search depends on the public LeanSearch and Loogle services (results are cached in `.work/`).

## License

MIT, see [LICENSE](LICENSE).
