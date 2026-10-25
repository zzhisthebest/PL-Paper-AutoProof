# AI Denotation Agent：研究计划文档

用 AI Agent 自动构造 Type Denotation / Logical Relation（及其推广到 abstract machine 等一般 PL 语义工作）的研究计划。
文档拆分为 **Benchmark**（近期，南京大学张子豪负责）与 **Solution**（后续探索，周喆负责）两部分。

## 目录结构

```
DenotationAgent/
├── main.tex                          # 主文档（中文，ctexart，xelatex 编译）
├── sections/
│   ├── 01-core-idea.tex              # 核心想法与定位
│   ├── 02-background.tex             # 背景与动机
│   ├── 03-benchmark.tex              # Benchmark：任务集定义（张子豪）
│   ├── 04-solution.tex               # Solution：Agent 系统与科学问题
│   └── 05-roadmap.tex                # 路线图、分工、与北大数院合作
├── bibliography.bib                  # 参考文献
├── docs/
│   ├── benchmark-proposal-2026-08.md # 重写后的沟通稿（可直接转发给张子豪）
│   └── original-idea-2026-07-27.md   # 原始想法 md（存档）
└── README.md
```

## 编译

```bash
xelatex main.tex
bibtex main
xelatex main.tex
xelatex main.tex
```

或一行：

```bash
latexmk -xelatex main.tex
```

## 主要内容

- **核心想法**：让 AI Agent 自动构造 PL 论文中最关键的语义不变量（type denotation / term denotation / logical relation / semantic domain），而非仅写 proof script。
- **Benchmark（§3）**：统一问题卡片格式；三类类型系统任务（复现 / 迁移 / 补全）；推广到 abstract machine 线（AAM、ADI、refocusing、refunctionalization、ICFP'26 staged evaluator pearl）；P0–P3 优先级；交付物四件套；里程碑。
- **Solution（§4）**：Agent 迭代工作流（candidate denotation → 逐条证明 → 失败分析 → 修改）；关键技术挑战；证明框架负担比较的科学问题。
- **路线图（§5）**：阶段 0–3 分工，以及与北京大学数学科学学院的远期合作。

## 实验结果

### 新难度标准：GPT-6 Luna high

每个难度36题，每题预算60分钟，并行100；未完成时续接原会话，共用剩余预算。本轮 Hard 成功 **19/36**，Medium **25/36**，Easy **31/36**。

![新难度标准下的累计证明成功数](benchmarkResults/figures/gpt6luna_high_difficulty_v4_full_r1_solved_over_time.png)

横轴为每题耗时（分钟），纵轴为在该时间内累计证明成功的题数。结果 tag：`gpt6luna_high_difficulty_v4_full_r1`。

### 历史实验

- [GPT-6 Sol High 结果与失败分析](docs/gpt6sol-high-results.md)

## Benchmark Cases表

`N` = Strong Normalization，`P` = Polymorphic Identity 自由定理，`RS` = Refinement Type Safety，`NI` = Noninterference。表格中的编号链接到对应题目，空白表示未提供。

题目名称统一为 `编号__语言__目标性质__features__难度`，例如 `001__stlc__strong-normalization__none__hard`。编号按任务类别、feature 组合、Hard / Medium / Easy 分配；编号不代表难度排名，新增题目从 109 起追加，不重新编号。

编号范围：001–024 STLC normalization；025–048 System F normalization；049–072 System F polymorphic identity；073–096 System F refinement type safety；097–108 Secure STLC noninterference。新旧名称对照保存在 [case-names.json](benchmarks/case-names.json)。运行时支持编号、完整名称和旧名称，例如 `python scripts/test.py --benchmark 001 --tag my_run`。

| 难度 | 提供的内容 | 需要完成 |
|---|---|---|
| Hard | 语言定义、目标定理陈述 | 自行构造 LR 及其环境解释，提出并证明所需辅助引理和 fundamental theorem，证明目标定理 |
| Medium | Hard 的全部内容 + 已证明的基础辅助引理（新鲜变量、环境查找、局部封闭、值、归约组合等） | 自行构造 LR 及其环境解释，提出并证明其余辅助引理和 fundamental theorem，证明目标定理 |
| Easy | Medium 的全部内容 + 替换、类型、求值等辅助证明 + 参考 LR、语义环境及基本性质 | 补全所需辅助证明，证明核心语义分支、fundamental theorem 和目标定理；可使用参考 LR，也可自行构造其他 LR |

三个难度均需证明 fundamental theorem 和目标定理，区别在于提供多少定义及已证明的辅助引理。Easy 中的参考 fundamental theorem 陈述仅作为注释提示，可按所选 LR 调整；其证明仍由 Agent 完成。输入文件只为目标定理预留证明位置，所需的中间定义和定理由 Agent 补入。三个难度的信息逐层包含，目标定理保持一致。

完整运行108个 cases：`bash scripts/run_test.sh`。默认 GPT-6 Luna high、每题3600秒、并行100；提前结束但未通过检查时续接原会话，共用剩余预算。新结果使用 tag `gpt6luna_high_difficulty_v4_full_r1`，保留历史结果。输入及已提供引理清单见 [difficulty-manifest.json](benchmarks/difficulty-manifest.json)。

每个 tag 的运行结果统一写入 `benchmarkResults/results_<tag>.json`，以完整题名为键，记录状态、耗时和 token 用量。并行写入采用文件锁和原子替换。证明和 traces 仍保存在各题目录；已有的旧格式结果仍可识别并跳过。

Secure STLC 基于 [SLam calculus](https://doi.org/10.1145/268946.268976) 的 secrecy 片段改编，目标性质为 noninterference。

| Feature | STLC-N-Hard | STLC-N-Medium | STLC-N-Easy | SystemF-N-Hard | SystemF-N-Medium | SystemF-N-Easy | SystemF-P-Hard | SystemF-P-Medium | SystemF-P-Easy | SystemF-RS-Hard | SystemF-RS-Medium | SystemF-RS-Easy | SecureSTLC-NI-Hard | SecureSTLC-NI-Medium | SecureSTLC-NI-Easy |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| None | [001](benchmarks/001__stlc__strong-normalization__none__hard) | [002](benchmarks/002__stlc__strong-normalization__none__medium) | [003](benchmarks/003__stlc__strong-normalization__none__easy) | [025](benchmarks/025__system-f__strong-normalization__none__hard) | [026](benchmarks/026__system-f__strong-normalization__none__medium) | [027](benchmarks/027__system-f__strong-normalization__none__easy) | [049](benchmarks/049__system-f__polymorphic-identity__none__hard) | [050](benchmarks/050__system-f__polymorphic-identity__none__medium) | [051](benchmarks/051__system-f__polymorphic-identity__none__easy) | [073](benchmarks/073__system-f-refinement__type-safety__none__hard) | [074](benchmarks/074__system-f-refinement__type-safety__none__medium) | [075](benchmarks/075__system-f-refinement__type-safety__none__easy) | [097](benchmarks/097__secure-stlc__noninterference__none__hard) | [098](benchmarks/098__secure-stlc__noninterference__none__medium) | [099](benchmarks/099__secure-stlc__noninterference__none__easy) |
| If-then-else | [004](benchmarks/004__stlc__strong-normalization__if__hard) | [005](benchmarks/005__stlc__strong-normalization__if__medium) | [006](benchmarks/006__stlc__strong-normalization__if__easy) | [028](benchmarks/028__system-f__strong-normalization__if__hard) | [029](benchmarks/029__system-f__strong-normalization__if__medium) | [030](benchmarks/030__system-f__strong-normalization__if__easy) | [052](benchmarks/052__system-f__polymorphic-identity__if__hard) | [053](benchmarks/053__system-f__polymorphic-identity__if__medium) | [054](benchmarks/054__system-f__polymorphic-identity__if__easy) | [076](benchmarks/076__system-f-refinement__type-safety__if__hard) | [077](benchmarks/077__system-f-refinement__type-safety__if__medium) | [078](benchmarks/078__system-f-refinement__type-safety__if__easy) | [100](benchmarks/100__secure-stlc__noninterference__if__hard) | [101](benchmarks/101__secure-stlc__noninterference__if__medium) | [102](benchmarks/102__secure-stlc__noninterference__if__easy) |
| Non-determinism | [007](benchmarks/007__stlc__strong-normalization__nondeterminism__hard) | [008](benchmarks/008__stlc__strong-normalization__nondeterminism__medium) | [009](benchmarks/009__stlc__strong-normalization__nondeterminism__easy) | [031](benchmarks/031__system-f__strong-normalization__nondeterminism__hard) | [032](benchmarks/032__system-f__strong-normalization__nondeterminism__medium) | [033](benchmarks/033__system-f__strong-normalization__nondeterminism__easy) | [055](benchmarks/055__system-f__polymorphic-identity__nondeterminism__hard) | [056](benchmarks/056__system-f__polymorphic-identity__nondeterminism__medium) | [057](benchmarks/057__system-f__polymorphic-identity__nondeterminism__easy) | [079](benchmarks/079__system-f-refinement__type-safety__nondeterminism__hard) | [080](benchmarks/080__system-f-refinement__type-safety__nondeterminism__medium) | [081](benchmarks/081__system-f-refinement__type-safety__nondeterminism__easy) | | | |
| Recursion | [010](benchmarks/010__stlc__strong-normalization__recursion__hard) | [011](benchmarks/011__stlc__strong-normalization__recursion__medium) | [012](benchmarks/012__stlc__strong-normalization__recursion__easy) | [034](benchmarks/034__system-f__strong-normalization__recursion__hard) | [035](benchmarks/035__system-f__strong-normalization__recursion__medium) | [036](benchmarks/036__system-f__strong-normalization__recursion__easy) | [058](benchmarks/058__system-f__polymorphic-identity__recursion__hard) | [059](benchmarks/059__system-f__polymorphic-identity__recursion__medium) | [060](benchmarks/060__system-f__polymorphic-identity__recursion__easy) | [082](benchmarks/082__system-f-refinement__type-safety__recursion__hard) | [083](benchmarks/083__system-f-refinement__type-safety__recursion__medium) | [084](benchmarks/084__system-f-refinement__type-safety__recursion__easy) | [103](benchmarks/103__secure-stlc__noninterference__recursion__hard) | [104](benchmarks/104__secure-stlc__noninterference__recursion__medium) | [105](benchmarks/105__secure-stlc__noninterference__recursion__easy) |
| If-then-else + Non-determinism | [013](benchmarks/013__stlc__strong-normalization__if+nondeterminism__hard) | [014](benchmarks/014__stlc__strong-normalization__if+nondeterminism__medium) | [015](benchmarks/015__stlc__strong-normalization__if+nondeterminism__easy) | [037](benchmarks/037__system-f__strong-normalization__if+nondeterminism__hard) | [038](benchmarks/038__system-f__strong-normalization__if+nondeterminism__medium) | [039](benchmarks/039__system-f__strong-normalization__if+nondeterminism__easy) | [061](benchmarks/061__system-f__polymorphic-identity__if+nondeterminism__hard) | [062](benchmarks/062__system-f__polymorphic-identity__if+nondeterminism__medium) | [063](benchmarks/063__system-f__polymorphic-identity__if+nondeterminism__easy) | [085](benchmarks/085__system-f-refinement__type-safety__if+nondeterminism__hard) | [086](benchmarks/086__system-f-refinement__type-safety__if+nondeterminism__medium) | [087](benchmarks/087__system-f-refinement__type-safety__if+nondeterminism__easy) | | | |
| If-then-else + Recursion | [016](benchmarks/016__stlc__strong-normalization__if+recursion__hard) | [017](benchmarks/017__stlc__strong-normalization__if+recursion__medium) | [018](benchmarks/018__stlc__strong-normalization__if+recursion__easy) | [040](benchmarks/040__system-f__strong-normalization__if+recursion__hard) | [041](benchmarks/041__system-f__strong-normalization__if+recursion__medium) | [042](benchmarks/042__system-f__strong-normalization__if+recursion__easy) | [064](benchmarks/064__system-f__polymorphic-identity__if+recursion__hard) | [065](benchmarks/065__system-f__polymorphic-identity__if+recursion__medium) | [066](benchmarks/066__system-f__polymorphic-identity__if+recursion__easy) | [088](benchmarks/088__system-f-refinement__type-safety__if+recursion__hard) | [089](benchmarks/089__system-f-refinement__type-safety__if+recursion__medium) | [090](benchmarks/090__system-f-refinement__type-safety__if+recursion__easy) | [106](benchmarks/106__secure-stlc__noninterference__if+recursion__hard) | [107](benchmarks/107__secure-stlc__noninterference__if+recursion__medium) | [108](benchmarks/108__secure-stlc__noninterference__if+recursion__easy) |
| Non-determinism + Recursion | [019](benchmarks/019__stlc__strong-normalization__nondeterminism+recursion__hard) | [020](benchmarks/020__stlc__strong-normalization__nondeterminism+recursion__medium) | [021](benchmarks/021__stlc__strong-normalization__nondeterminism+recursion__easy) | [043](benchmarks/043__system-f__strong-normalization__nondeterminism+recursion__hard) | [044](benchmarks/044__system-f__strong-normalization__nondeterminism+recursion__medium) | [045](benchmarks/045__system-f__strong-normalization__nondeterminism+recursion__easy) | [067](benchmarks/067__system-f__polymorphic-identity__nondeterminism+recursion__hard) | [068](benchmarks/068__system-f__polymorphic-identity__nondeterminism+recursion__medium) | [069](benchmarks/069__system-f__polymorphic-identity__nondeterminism+recursion__easy) | [091](benchmarks/091__system-f-refinement__type-safety__nondeterminism+recursion__hard) | [092](benchmarks/092__system-f-refinement__type-safety__nondeterminism+recursion__medium) | [093](benchmarks/093__system-f-refinement__type-safety__nondeterminism+recursion__easy) | | | |
| If-then-else + Non-determinism + Recursion | [022](benchmarks/022__stlc__strong-normalization__if+nondeterminism+recursion__hard) | [023](benchmarks/023__stlc__strong-normalization__if+nondeterminism+recursion__medium) | [024](benchmarks/024__stlc__strong-normalization__if+nondeterminism+recursion__easy) | [046](benchmarks/046__system-f__strong-normalization__if+nondeterminism+recursion__hard) | [047](benchmarks/047__system-f__strong-normalization__if+nondeterminism+recursion__medium) | [048](benchmarks/048__system-f__strong-normalization__if+nondeterminism+recursion__easy) | [070](benchmarks/070__system-f__polymorphic-identity__if+nondeterminism+recursion__hard) | [071](benchmarks/071__system-f__polymorphic-identity__if+nondeterminism+recursion__medium) | [072](benchmarks/072__system-f__polymorphic-identity__if+nondeterminism+recursion__easy) | [094](benchmarks/094__system-f-refinement__type-safety__if+nondeterminism+recursion__hard) | [095](benchmarks/095__system-f-refinement__type-safety__if+nondeterminism+recursion__medium) | [096](benchmarks/096__system-f-refinement__type-safety__if+nondeterminism+recursion__easy) | | | |
