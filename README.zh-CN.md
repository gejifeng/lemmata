# lean_prover

一个用 **Lean 4 + Mathlib** 证明竞赛数学题的小型 LLM 智能体，Lean 编译器是唯一的裁判。它为在单个本地部署的
开源权重模型上运行而设计，在 [PutnamBench](https://github.com/trishullab/PutnamBench) 上评测。

[English](README.md)

## 成果

下面列出的证明都在 [`results/proofs/`](results/proofs) 中。每一份都用 `python -m lean_prover.report`
从零重新检查过：

- 定理陈述与 PutnamBench 完全一致；
- 证明不含 `sorry`；
- 证明只依赖标准公理 `propext`、`Classical.choice`、`Quot.sound`。

| 题集 | 已验证 |
|---|---|
| 主题集：开发过程中使用的 13 道 PutnamBench 题 | **6 / 13** |
| 简单题集：另外 20 道、以初等为主的 PutnamBench 题 | **19 / 20** |
| **合计** | **25 / 33** |

所有实验的设置：

- **模型：** 单个开源权重模型（`qwen3.8-flash-next`），用 vLLM 本地部署，开启 thinking 使用。
- **吞吐：** 最多 8 个并发请求，总输出约 90 token/秒，单个请求约 12 token/秒。
- **Lean：** v4.28.0，Mathlib v4.28.0。
- **花费：** 下文各轮实验共生成约 2100 万 token。

有些题在一轮里解出，有些是后续几轮复用了已证引理和之前的尝试才解出。单轮对比见下一节。

<details>
<summary>逐题结果</summary>

| 题目 | 领域 | 结果 |
|---|---|---|
| putnam_2001_a1 | 代数（二元运算） | ✅（自动化层，没有调用模型） |
| putnam_1992_a1 | 函数方程 | ✅ |
| putnam_1993_a2 | 递推数列 | ✅ |
| putnam_1966_a1 | 求和、整数除法 | ✅（拆成 3 个引理） |
| putnam_1963_a2 | 积性函数 | ✅（拆成 5 个引理） |
| putnam_1965_b5 | 图论（无三角形图） | ✅（拆成 7 个引理，分 4 轮证完） |
| putnam_1999_a2 | 实多项式、平方和 | ❌ 7 个引理证出 6 个，卡在因式分解引理 |
| putnam_1969_a2 | 行列式 | ❌ |
| putnam_2000_a4 | 瑕积分 | ❌ |
| putnam_1962_a1 | 平面几何（凸位置） | ❌ |
| putnam_1964_a1 | 平面几何（距离） | ❌ 需要 Jung 定理，Mathlib 中没有 |
| putnam_1965_a1 | 平面几何（角） | ❌ |
| putnam_1976_b3 | 概率 | ❌ |
| 简单题集（20 题） | 数论、代数、组合、分析 | ✅ 19 题，❌ putnam_2001_a5 |

</details>

### 什么起了作用：同样 20 道题、同样 6 小时、同一个模型

| 轮次 | 策略 | 解出 | 生成 token | 每解一题的 token |
|---|---|---|---|---|
| e1（基线） | 直接证明与一份拆分竞速 | 8 / 20 | 171 万 | 约 21 万 |
| e2 | + Mathlib 检索、确定性修复、非形式计划、2 份并行骨架 | 7 / 20 | 174 万 | 约 25 万 |
| e3 | e2 + 严格公平调度 | 4 / 20 | 170 万 | 约 42 万 |
| **e4** | **便宜的先做，只在停滞时拆分**（当前默认） | **13 / 20** | 192 万 | **约 15 万** |

这几轮说明了：

1. **调度影响最大。**
   - 在这个吞吐下，预先写非形式计划和并行骨架得不偿失。e3 在 6 小时里只做了 39 次证明尝试。
   - 现在的默认做法是：先用便宜的手段，只有进展停滞时才拆分。
2. **检索和确定性修复减少了白白浪费的轮次。**
   - 失败尝试中出现"名字不存在"的比例从 32% 降到 15%。
   - 用完输出预算的尝试从 5 次降到 0。
3. **拆分加引理缓存，让难题能跨轮积累进展。** putnam_1965_b5 的 7 个引理是在 4 轮里陆续证出的。
4. **剩下的难题受限于模型，而不是框架。** 每道题都卡在一个核心步骤上，这一步需要 60–200 行的技术性证明：
   - 每个步骤尝试了 50–130 次，错误数不再下降；
   - 模型常常把最难的那一步留成 `sorry`；
   - 它也无法把这一步再拆小；
   - 单纯因为名字写错而失败的只占约 9%。

## 工作原理

```
题目 ──▶ 自动化层 ──▶ 直接证明 ─────停滞──▶ 拆分 ──────────▶ 每个引理：走同样的流程（递归）
         (不调用模型)   thinking → 编译 →     带 `sorry` 引理     (深度 ≤ 3；引理缓存；
                        便宜的修复            的骨架              假引理尽早剔除)
```

- **Lean 是唯一的裁判。**
  - 定理陈述在构造上就是固定的。
  - 候选证明只有在编译通过、不含 `sorry`、且 `#print axioms` 只显示标准公理时才被接受。
  - 其他一切（非形式证明、骨架、检索结果）都只是参考，永远不会中止运行。
- **自动化层**（`decompose.try_automation`），在任何模型调用之前：
  - `omega`、`linarith`、`positivity`、`norm_num`、`simp_all`、`ring`、`decide`、`grind`、`aesop`、`nlinarith`、`field_simp`；
  - `exact?`（Mathlib 库搜索），它给出的建议会被替换进证明。
- **直接证明**（`agent.run_chain`）：
  - 一次 thinking 尝试写出完整证明。
  - Lean 的报错返回给模型。对不存在的名字，会附上真实的 Mathlib 名字及其类型，来自一个包含 45 万条声明的本地索引。
  - 随后最多 4 次便宜的非 thinking 修复请求，每次采样 2 个候选。
  - 如果 thinking 预算用完，会用一次非 thinking 的后续请求，把已有的推理转成代码。
- **确定性修复，不消耗模型 token**（`autopatch.py`）：
  - 出错的 `have` 步骤，替换成一组以 `exact?` 结尾的自动化 tactic；
  - 被报告为 "No goals to be solved" 的 tactic 直接删除。
- **Mathlib 检索**（`search.py`）：
  - 自然语言查询用 [LeanSearch](https://leansearch.net)，常量/类型模式用 [Loogle](https://loogle.lean-lang.org)。
  - 每个结果都要在本地 Mathlib 里核对，因为这两个服务索引的是更新的版本。
  - 检索用在三个地方：第一次尝试之前；模型可以自己写 ```` ```search ```` 块发起检索；出现名字不存在的错误时。
- **拆分**（`decompose.py`）：
  - 模型写一个 Lean 骨架，其中的辅助引理先用 `sorry` 占位。
  - 骨架必须能编译；只是把原定理换个说法的骨架会被拒绝。
  - 每个引理递归求解。
  - 引理先用 `plausible` 找反例；如果是假引理，就放弃这个骨架，并把原因反馈给下一份骨架。
  - 如果一次直接尝试除了 `sorry` 缺口外都能编译，会自动把它变成骨架（`harvest.py`），每个缺口的精确目标来自 `extract_goal`。
- **调度**（`llm.py`、`agent.py`）：
  - 对模型请求用优先级队列。
  - 一道题已用的调用越多（公平份额）、或者陷入停滞，优先级就越低；子引理有一点小的加成。
- **跨轮持久化：**
  - 已证引理按陈述缓存；
  - 新一轮从同一陈述之前最好的尝试开始（`history.py`）；
  - 合格的骨架可以复用（`--resume-from`）。

## 安装

需要：

- Linux；
- Python ≥ 3.10（只用标准库，没有依赖）；
- `git` 和 `curl`；
- 约 10 GB 磁盘空间给 Mathlib；
- 一个 OpenAI 兼容的 chat 接口。

thinking 的开关通过 vLLM 的 `chat_template_kwargs.enable_thinking` 控制（Qwen 风格的 chat 模板），
其他服务端可能会忽略这个字段。

```bash
git clone <本仓库> lean_prover && cd lean_prover
./scripts/setup.sh          # elan + Lean、Mathlib 缓存、PutnamBench、Mathlib 名字索引（约 30 分钟）

export LEAN_PROVER_BASE_URL=http://localhost:8000/v1   # OpenAI 兼容接口
export LEAN_PROVER_MODEL=<服务端的模型名>
export LEAN_PROVER_API_KEY=...                          # 可选
```

## 使用

```bash
# 证明题目（输出在 runs/<run>/；每道解出的题有 FINAL_proof.lean）
python -m lean_prover.campaign --set easy --hours 6 --run my_run
python -m lean_prover.campaign putnam_1977_a5 putnam_1988_b1 --hours 1

# 继续攻难题，复用之前几轮的骨架（引理缓存和最好的尝试会自动复用）
python -m lean_prover.campaign --set main --hours 12 --run my_run2 --resume-from my_run

# 从零重新验证所有已解出的题，并汇总到 results/proofs/
python -m lean_prover.report all

# 单轮统计：解出的题、每题 token、错误类别
python -m lean_prover.metrics my_run

# 离线端到端自测（脚本化的假模型 + 真实 Lean；不调用模型）
python -m lean_prover.selftest
```

搜索设置在 [`config/default.json`](config/default.json)。这个文件每次使用时都会重新读取，所以可以在运行中修改。
主要参数：

| 键 | 默认值 | 含义 |
|---|---|---|
| `stall_rounds` | 2 | 编译错误数连续多少轮 thinking 没有减少就开始拆分 |
| `race_top` | false | 一开始就让拆分与直接证明并行（`--resume-from` 提供了骨架时总是开启） |
| `quick_repairs` / `repair_samples` | 4 / 2 | 每次 thinking 尝试之后的非 thinking 修复请求数，以及每次请求的采样数 |
| `think_max_tokens` | 14000 | 一次 thinking 尝试的输出预算 |
| `search` | true | Mathlib 检索 |
| `two_stage` | false | 形式化之前先写非形式计划（在我们的吞吐下反而更差） |
| `fair_share_calls` | 3 | 一道题每用掉 N 次模型调用，优先级降 1 |
| `resume_previous` / `lemma_cache` | true / true | 复用之前几轮的尝试和引理 |

环境变量：

| 变量 | 默认值 | 含义 |
|---|---|---|
| `LEAN_PROVER_LLM_JOBS` | 6 | 并发 thinking 请求数 |
| `LEAN_PROVER_QUICK_JOBS` | 2 | 并发非 thinking 请求数 |
| `LEAN_PROVER_COMPILE_JOBS` | 10 | 并发 Lean 编译数 |
| `PUTNAMBENCH_DIR` | `benchmarks/PutnamBench/lean4/src` | PutnamBench 源文件目录 |
| `LEAN_PROVER_RUNS_DIR` | `runs/` | 运行输出目录 |
| `LEAN_PROVER_WORK_DIR` | `.work/` | 临时文件、缓存、名字索引 |
| `LEAN_PROVER_CONFIG` | `config/default.json` | 搜索设置文件 |

## 目录结构

```
lean_prover/
  campaign.py    命令行：并行处理一组题目
  decompose.py   solve()：自动化 → 直接证明 → 拆分（递归）、引理缓存、真假检查
  agent.py       直接证明链、提示词、反馈、运行期配置
  problem.py     解析 PutnamBench、提取候选证明、渲染与接受检查
  lean.py        `lake env lean --json` 封装、公理检查、编译缓存
  llm.py         流式 OpenAI 兼容客户端、优先级调度、thinking 预算挽救
  search.py      LeanSearch / Loogle 检索，并对照本地 Mathlib 核验
  names.py       为不存在的标识符推荐真实名字
  autopatch.py   确定性修复（自动化 tactic 组合 + exact?、删除多余 tactic）
  harvest.py     用 `extract_goal` 把 `sorry` 缺口变成引理
  history.py     每个陈述之前最好的尝试
  report.py      对所有证明做独立重新验证
  metrics.py     单轮统计
  selftest.py    离线端到端测试
  benchmarks.py  题集
config/default.json   搜索设置
scripts/              安装脚本与 Mathlib 名字索引生成器
results/proofs/       25 份已验证的证明
```

## 局限

- 受吞吐限制：总共约 90 token/秒，一次 thinking 尝试要 20–30 分钟，所以难点只能尝试几十到一百来次。
  能解出这类题的系统，通常用强化学习训练过的证明模型，采样次数多得多。
- 几何和测度论概率是最弱的领域。
- 支持需要给出答案的题（带 `solution` 定义），但与 PutnamBench 一样，答案本身只由证明来检验。
- 检索依赖公开的 LeanSearch 和 Loogle 服务（结果缓存在 `.work/`）。

## 许可证

MIT，见 [LICENSE](LICENSE)。
