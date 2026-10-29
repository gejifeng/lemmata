# Lemmata

A small LLM agent that proves mathematics in **Lean 4 + Mathlib**, with the Lean compiler as the only judge.
State a problem in plain language (or in Lean) in a local web UI, confirm the Lean statement it is translated
into, and get a proof that Lean has checked. It uses the DeepSeek API by default and also runs on a single locally
served open-weight model (vLLM), which is how it was evaluated on [PutnamBench](https://github.com/trishullab/PutnamBench).

[中文说明](README.zh-CN.md)

## Quick start

**Windows:** download this repository (Code → Download ZIP, or `git clone`) into a short path such as
`C:\lemmata`, then double-click **`install.bat`**. It installs whatever is missing (Python, Git, Lean via
elan), downloads Mathlib (several GB), builds a Mathlib name index (10–20 minutes, once), asks for your DeepSeek
API key, puts a `Lemmata` shortcut on the desktop and opens the web UI. Later, start it with the shortcut or
`start_webui.bat`.

**Linux / macOS:**

```bash
git clone https://github.com/gejifeng/lemmata.git && cd lemmata
./install.sh
```

It does the same: checks Python 3.10+ and Git (and prints the command to install them if missing), installs Lean
via elan, downloads Mathlib, builds the name index, asks for your API key, adds `Lemmata` to the application menu
(a `Lemmata.command` on the desktop on macOS) and opens the web UI. Later, start it with the launcher or
`./start_webui.sh`. Options: `--skip-name-index`, `--skip-putnambench`, `--no-shortcut`, `--no-webui`.

Get an API key at [platform.deepseek.com](https://platform.deepseek.com) and enter it under **Settings** in the
web UI (it is stored only in `.env` in the project folder). Then:

1. **Natural language** tab: write the statement, e.g. *Prove that n³ − n is divisible by 6 for every integer n*,
   and click **Formalize**. The model writes a Lean statement; Lean checks that it compiles (errors go back to the
   model up to 3 times); a second request that sees only the Lean code explains what it literally says.
2. **Check the Lean statement against your problem** and edit it if needed (**Check statement** re-compiles it).
   This is the one step Lean cannot check: a proof is a proof of the Lean statement, not of the sentence you wrote.
   For "find all ..." problems the statement contains the answer the model proposed.
3. Pick the model (`deepseek-v4-flash` by default, `deepseek-v4-pro` is stronger) and a time limit, then **Prove**.
   The job page shows the live log and, when it succeeds, the verified proof to copy or download. Jobs keep running
   if you close the page; stopping the web UI stops them.

The **Lean code** tab takes a Lean statement directly: `import Mathlib`, optional definitions, and one
`theorem name ... := by sorry`.

## Results

All proofs listed here are in [`results/proofs/`](results/proofs). Each one was re-checked from scratch with
`python3 -m lemmata.report`:

- the theorem statement is identical to PutnamBench;
- the proof contains no `sorry`;
- the proof depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

| Problem set | Verified |
|---|---|
| Main set: 13 PutnamBench problems used during development | **6 / 13** |
| Easy set: 20 additional, mostly elementary PutnamBench problems | **19 / 20** |
| **Total** | **25 / 33** |

Setup for all experiments:

- **Model:** one open-weight model (`qwen3.8-flash-next`, quantized) served locally by vLLM, used with thinking enabled.
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

## Setup details

Requirements: Windows 10/11, Linux or macOS; Python ≥ 3.10 (standard library only, no `pip install` needed);
`git`; about 10 GB of disk for Mathlib; and a model endpoint (the DeepSeek API by default). The installers above
take care of the rest and can be run again safely: finished steps are skipped.

All settings are read from `.env` at the project root, which is git-ignored; see [`.env.example`](.env.example).
The web UI's Settings writes the same file. Variables already set in the shell take precedence, and another file
can be used with `LEMMATA_ENV_FILE=/path/to/file`.

Other endpoints are selected with `LEMMATA_API_STYLE`:

| Style | Thinking on/off | Use for |
|---|---|---|
| `deepseek` (default) | `thinking: {type: enabled/disabled}` | the DeepSeek API |
| `vllm` | `chat_template_kwargs.enable_thinking` (Qwen-style templates); also uses `n` and assistant prefill | a local vLLM server |
| `openai` | not sent (`reasoning_effort` if set) | any other OpenAI-compatible endpoint |

Every run first sends one tiny request to the endpoint and stops with the server's error message if it fails.

## Usage

The web UI covers the usual workflow. The same steps are available from the command line (on Windows use
`python` or `py -3` instead of `python3`):

```bash
# web UI (options: --port 7860, --no-browser, --host for access from other machines)
python3 -m lemmata.webui

# natural language -> Lean statement, printed with Lean's verdict and the independent explanation
python3 -m lemmata.formalize "Prove that n^3 - n is divisible by 6 for every integer n."

# prove your own Lean file (one `theorem name ... := by sorry` after `import Mathlib` and optional definitions)
python3 -m lemmata.campaign my_theorem.lean --hours 1

# PutnamBench problems (outputs in runs/<run>/; FINAL_proof.lean for each solved problem)
python3 -m lemmata.campaign putnam_1977_a5 putnam_1988_b1 --hours 1
python3 -m lemmata.campaign --set easy --hours 6 --run my_run

# continue hard problems, reusing skeletons from earlier runs (lemma cache and best attempts are reused automatically)
python3 -m lemmata.campaign --set main --hours 12 --run my_run2 --resume-from my_run

# re-verify all solved PutnamBench problems from scratch and collect them into results/proofs/
python3 -m lemmata.report all

# per-run statistics: solved problems, tokens per problem, error categories
python3 -m lemmata.metrics my_run

# offline end-to-end self-test (scripted fake model, real Lean; no model calls)
python3 -m lemmata.selftest
```

Search settings are in [`config/default.json`](config/default.json). The defaults are the configuration that
solved the most problems in the comparison above (e4: cheap attempts first, decompose only on stall). The file is
re-read on every use, so it can be edited while a campaign runs. The main knobs:

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

Environment variables (set them in `.env` or in the shell):

| Variable | Default | Meaning |
|---|---|---|
| `LEMMATA_API_KEY` | (empty) | API key, sent as `Authorization: Bearer ...` |
| `LEMMATA_MODEL` | `deepseek-v4-flash` | model name served at the endpoint |
| `LEMMATA_BASE_URL` | `https://api.deepseek.com` | OpenAI-compatible endpoint |
| `LEMMATA_API_STYLE` | `deepseek` | `deepseek`, `vllm` or `openai` (see above) |
| `LEMMATA_REASONING_EFFORT` | (empty) | sent as `reasoning_effort` with thinking requests when set |
| `LEMMATA_LLM_JOBS` | 6 | concurrent thinking requests |
| `LEMMATA_QUICK_JOBS` | 2 | concurrent non-thinking requests |
| `LEMMATA_COMPILE_JOBS` | half the CPU cores, ≤ 10 | concurrent Lean compilations (1–2 GB of RAM each) |
| `PUTNAMBENCH_DIR` | `benchmarks/PutnamBench/lean4/src` | PutnamBench sources |
| `LEMMATA_RUNS_DIR` | `runs/` | campaign output directory (web UI jobs are `runs/web_*`) |
| `LEMMATA_WORK_DIR` | `.work/` | scratch files, caches, name index |
| `LEMMATA_CONFIG` | `config/default.json` | search settings file |

## Repository layout

```
lemmata/
  webui.py       local web UI server (standard library); runs each proof as a campaign subprocess
  web/index.html the web UI page
  formalize.py   natural language -> compiling Lean statement + independent explanation
  campaign.py    command line: run a set of problems (Lean files or PutnamBench names) in parallel
  decompose.py   solve(): automation → direct attempts → decomposition (recursive), lemma cache, falsity check
  agent.py       direct proof chains, prompts, feedback, runtime config
  problem.py     problem parsing (PutnamBench, user Lean files), candidate extraction, rendering, acceptance check
  lean.py        `lake env lean --json` wrapper, axiom check, compile cache
  llm.py         streaming client (DeepSeek / vLLM / OpenAI styles), priority scheduling, thinking-budget salvage
  search.py      LeanSearch / Loogle retrieval checked against the local Mathlib
  names.py       real-name suggestions for unknown identifiers
  autopatch.py   deterministic repairs (automation combo + exact?, dead-tactic removal)
  harvest.py     turn `sorry` gaps into lemmas via `extract_goal`
  history.py     best earlier attempt per statement
  report.py      independent re-verification of all proofs
  metrics.py     run statistics
  selftest.py    offline end-to-end test
  benchmarks.py  problem sets
  dotenv.py      `.env` loader and writer
config/default.json   search settings
install.bat           Windows one-click setup (runs scripts/install.ps1)
install.sh            Linux/macOS one-click setup (runs scripts/setup.sh)
start_webui.bat/.sh   start the web UI
scripts/              setup scripts and the Mathlib name-index generator
.env.example          template for model endpoint, API key, concurrency and paths
results/proofs/       the 25 verified proofs
```

## Limitations

- Formalization is checked by you, not by Lean. The independent explanation helps spot mistranslations, but a
  wrong statement (a missing hypothesis, ℕ instead of ℝ, a wrong answer) is proved just as happily as a right one.
- Throughput-bound in the local setup used for the results: with about 90 tokens/s, a thinking attempt takes 20–30 minutes, so hard steps get only
  tens to a hundred attempts. Systems that solve such problems typically use RL-trained provers with far more samples.
- Geometry and measure-theoretic probability are the weakest areas.
- Answer-type problems (with a `solution` definition) are supported, but the answer itself is checked only by
  the proof, as in PutnamBench.
- Search depends on the public LeanSearch and Loogle services (results are cached in `.work/`).

## License

MIT, see [LICENSE](LICENSE).
