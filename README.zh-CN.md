# Lemmata

一个用 **Lean 4 + Mathlib** 证明数学命题的小型 LLM 智能体，Lean 编译器是唯一的裁判。在本地网页界面里用自然语言
（或直接用 Lean）写下命题，确认它被翻译成的 Lean 命题，就能得到一份经过 Lean 检查的证明。默认使用 DeepSeek API，
也可以在单个本地部署的开源权重模型（vLLM）上运行，下面在 [PutnamBench](https://github.com/trishullab/PutnamBench)
上的评测就是这样做的。

[English](README.md)

## 快速开始

**Windows：** 把本仓库下载（Code → Download ZIP，或 `git clone`）到一个较短的路径，比如 `C:\lemmata`，
然后双击 **`install.bat`**。它会安装缺少的软件（Python、Git、通过 elan 安装 Lean），下载 Mathlib（几 GB），
建立 Mathlib 名字索引（10–20 分钟，只需一次），询问你的 DeepSeek API Key，在桌面放一个 `Lemmata` 快捷方式，
并打开网页界面。以后用这个快捷方式或 `start_webui.bat` 启动。

**Linux / macOS：**

```bash
git clone https://github.com/gejifeng/lemmata.git && cd lemmata
./install.sh
```

它做的事情和 Windows 版一样：检查 Python 3.10+ 和 Git（缺少时给出对应系统的安装命令），通过 elan 安装 Lean，下载
Mathlib，建立名字索引，询问 API Key，在应用菜单里添加 `Lemmata`（macOS 上是桌面的 `Lemmata.command`），并打开网页界面。
以后用这个启动项或 `./start_webui.sh` 启动。选项：`--skip-name-index`、`--skip-putnambench`、`--no-shortcut`、`--no-webui`。

在 [platform.deepseek.com](https://platform.deepseek.com) 获取 API Key，填到网页界面的「设置」里（只保存在项目目录的
`.env` 文件中）。然后：

1. 在「自然语言」页写下命题，例如「证明：对任意整数 n，n³ − n 能被 6 整除」，点「形式化为 Lean 命题」。模型写出
   Lean 命题，Lean 检查它能否编译（出错会把错误交回模型，最多 3 次）；另一次只看 Lean 代码的独立请求会解释这个命题
   字面上说了什么。
2. **对照原题检查 Lean 命题**，需要时直接修改（「检查命题」会重新编译）。这是 Lean 无法替你检查的一步：证明的是
   Lean 命题，而不是你写的那句话。对「求所有……」这类题，命题里写的是模型给出的答案。
3. 选择模型（默认 `deepseek-v4-flash`，`deepseek-v4-pro` 更强）和时间上限，点「开始证明」。任务页面会显示实时日志，
   成功后给出已验证的证明，可以复制或下载。关掉网页任务也会继续运行；关闭网页界面的服务会停止任务。

「Lean 代码」页直接接受 Lean 命题：`import Mathlib`、可选的定义，以及一个 `theorem 名字 ... := by sorry`。

## 成果

下面列出的证明都在 [`results/proofs/`](results/proofs) 中。每一份都用 `python3 -m lemmata.report`
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

- **模型：** 单个开源权重模型（`qwen3.8-flash-next`，量化版），用 vLLM 本地部署，开启 thinking 使用。
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

## 安装细节

需要：Windows 10/11、Linux 或 macOS；Python ≥ 3.10（只用标准库，不需要 `pip install`）；`git`；约 10 GB 磁盘空间给
Mathlib；以及一个模型接口（默认 DeepSeek API）。其余的由上面的安装脚本完成，可以放心重复运行，已完成的步骤会跳过。

所有设置都从项目根目录的 `.env` 读取，这个文件已被 git 忽略；模板见 [`.env.example`](.env.example)。网页界面的
「设置」写的也是这个文件。在 shell 中已经设置的变量优先；也可以用 `LEMMATA_ENV_FILE=/path/to/file` 指定其他文件。

其他接口用 `LEMMATA_API_STYLE` 选择：

| 类型 | thinking 开关 | 适用于 |
|---|---|---|
| `deepseek`（默认） | `thinking: {type: enabled/disabled}` | DeepSeek API |
| `vllm` | `chat_template_kwargs.enable_thinking`（Qwen 风格模板）；还会用到 `n` 和 assistant 预填充 | 本地 vLLM 服务 |
| `openai` | 不发送（设置了 `reasoning_effort` 时发送它） | 其他 OpenAI 兼容接口 |

每次运行都会先向接口发一个很小的请求，失败时直接停止，并显示服务端返回的错误信息。

## 使用

常用流程都可以在网页界面完成。命令行也能做同样的事（Windows 上把 `python3` 换成 `python` 或 `py -3`）：

```bash
# 网页界面（选项：--port 7860、--no-browser、--host 允许其他机器访问）
python3 -m lemmata.webui

# 自然语言 -> Lean 命题，输出 Lean 的检查结果和独立解读
python3 -m lemmata.formalize "证明：对任意整数 n，n^3 - n 能被 6 整除。"

# 证明你自己的 Lean 文件（`import Mathlib`、可选定义之后，一个 `theorem 名字 ... := by sorry`）
python3 -m lemmata.campaign my_theorem.lean --hours 1

# PutnamBench 题目（输出在 runs/<run>/；每道解出的题有 FINAL_proof.lean）
python3 -m lemmata.campaign putnam_1977_a5 putnam_1988_b1 --hours 1
python3 -m lemmata.campaign --set easy --hours 6 --run my_run

# 继续攻难题，复用之前几轮的骨架（引理缓存和最好的尝试会自动复用）
python3 -m lemmata.campaign --set main --hours 12 --run my_run2 --resume-from my_run

# 从零重新验证所有已解出的 PutnamBench 题，并汇总到 results/proofs/
python3 -m lemmata.report all

# 单轮统计：解出的题、每题 token、错误类别
python3 -m lemmata.metrics my_run

# 离线端到端自测（脚本化的假模型 + 真实 Lean；不调用模型）
python3 -m lemmata.selftest
```

搜索设置在 [`config/default.json`](config/default.json)。默认值就是上面对比中解出题目最多的配置（e4：先做便宜的尝试，
停滞后才拆分）。这个文件每次使用时都会重新读取，所以可以在运行中修改。主要参数：

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

环境变量（写在 `.env` 里，或在 shell 中设置）：

| 变量 | 默认值 | 含义 |
|---|---|---|
| `LEMMATA_API_KEY` | （空） | API Key，作为 `Authorization: Bearer ...` 发送 |
| `LEMMATA_MODEL` | `deepseek-v4-flash` | 服务端的模型名 |
| `LEMMATA_BASE_URL` | `https://api.deepseek.com` | OpenAI 兼容接口地址 |
| `LEMMATA_API_STYLE` | `deepseek` | `deepseek`、`vllm` 或 `openai`（见上） |
| `LEMMATA_REASONING_EFFORT` | （空） | 设置后随 thinking 请求作为 `reasoning_effort` 发送 |
| `LEMMATA_LLM_JOBS` | 6 | 并发 thinking 请求数 |
| `LEMMATA_QUICK_JOBS` | 2 | 并发非 thinking 请求数 |
| `LEMMATA_COMPILE_JOBS` | CPU 核数的一半，最多 10 | 并发 Lean 编译数（每个占 1–2 GB 内存） |
| `PUTNAMBENCH_DIR` | `benchmarks/PutnamBench/lean4/src` | PutnamBench 源文件目录 |
| `LEMMATA_RUNS_DIR` | `runs/` | 运行输出目录（网页界面的任务在 `runs/web_*`） |
| `LEMMATA_WORK_DIR` | `.work/` | 临时文件、缓存、名字索引 |
| `LEMMATA_CONFIG` | `config/default.json` | 搜索设置文件 |

## 目录结构

```
lemmata/
  webui.py       本地网页界面服务（标准库）；每个证明作为一个 campaign 子进程运行
  web/index.html 网页界面
  formalize.py   自然语言 -> 可编译的 Lean 命题 + 独立解读
  campaign.py    命令行：并行处理一组题目（Lean 文件或 PutnamBench 题名）
  decompose.py   solve()：自动化 → 直接证明 → 拆分（递归）、引理缓存、真假检查
  agent.py       直接证明链、提示词、反馈、运行期配置
  problem.py     题目解析（PutnamBench、用户的 Lean 文件）、提取候选证明、渲染与接受检查
  lean.py        `lake env lean --json` 封装、公理检查、编译缓存
  llm.py         流式客户端（DeepSeek / vLLM / OpenAI 三种类型）、优先级调度、thinking 预算挽救
  search.py      LeanSearch / Loogle 检索，并对照本地 Mathlib 核验
  names.py       为不存在的标识符推荐真实名字
  autopatch.py   确定性修复（自动化 tactic 组合 + exact?、删除多余 tactic）
  harvest.py     用 `extract_goal` 把 `sorry` 缺口变成引理
  history.py     每个陈述之前最好的尝试
  report.py      对所有证明做独立重新验证
  metrics.py     单轮统计
  selftest.py    离线端到端测试
  benchmarks.py  题集
  dotenv.py      `.env` 读写
config/default.json   搜索设置
install.bat           Windows 一键安装（运行 scripts/install.ps1）
install.sh            Linux/macOS 一键安装（运行 scripts/setup.sh）
start_webui.bat/.sh   启动网页界面
scripts/              安装脚本与 Mathlib 名字索引生成器
.env.example          模型接口、API key、并发与路径的配置模板
results/proofs/       25 份已验证的证明
```

## 局限

- 形式化由你检查，而不是由 Lean 检查。独立解读有助于发现翻译错误，但一个错误的命题（少了假设、把 ℝ 写成 ℕ、
  答案错了）会和正确的命题一样被认真证明。
- 受吞吐限制（指上面结果所用的本地环境）：总共约 90 token/秒，一次 thinking 尝试要 20–30 分钟，所以难点只能尝试几十到一百来次。
  能解出这类题的系统，通常用强化学习训练过的证明模型，采样次数多得多。
- 几何和测度论概率是最弱的领域。
- 支持需要给出答案的题（带 `solution` 定义），但与 PutnamBench 一样，答案本身只由证明来检验。
- 检索依赖公开的 LeanSearch 和 Loogle 服务（结果缓存在 `.work/`）。

## 许可证

MIT，见 [LICENSE](LICENSE)。
