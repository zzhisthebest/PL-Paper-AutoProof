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

## Benchmark Cases表

`N` = Normalization，`P` = Parametricity；`Hard` = 不给 LR，`Medium` = 给 LR，`Easy` = 给 LR 和 fundamental theorem；`✔` = 已完成，空白 = 还没做完。

| Feature | STLC-N-Hard | STLC-N-Medium | STLC-N-Easy | SystemF-N-Hard | SystemF-N-Medium | SystemF-N-Easy | SystemF-P-Hard | SystemF-P-Medium | SystemF-P-Easy |
|---|---|---|---|---|---|---|---|---|---|
| None | [✔](benchmarks/stlc-normalization-none-hard) | [✔](benchmarks/stlc-normalization-none-medium) | [✔](benchmarks/stlc-normalization-none-easy) | [✔](benchmarks/systemf-normalization-none-hard) | [✔](benchmarks/systemf-normalization-none-medium) | [✔](benchmarks/systemf-normalization-none-easy) | [✔](benchmarks/systemf-parametricity-none-hard) | [✔](benchmarks/systemf-parametricity-none-medium) | [✔](benchmarks/systemf-parametricity-none-easy) |
| If-then-else | [✔](benchmarks/stlc-normalization-if-hard) | [✔](benchmarks/stlc-normalization-if-medium) | [✔](benchmarks/stlc-normalization-if-easy) | [✔](benchmarks/systemf-normalization-if-hard) | [✔](benchmarks/systemf-normalization-if-medium) | [✔](benchmarks/systemf-normalization-if-easy) | [✔](benchmarks/systemf-parametricity-if-hard) | [✔](benchmarks/systemf-parametricity-if-medium) | [✔](benchmarks/systemf-parametricity-if-easy) |
| Non-determinism | [✔](benchmarks/stlc-normalization-nondeterminism-hard) | [✔](benchmarks/stlc-normalization-nondeterminism-medium) | [✔](benchmarks/stlc-normalization-nondeterminism-easy) | [✔](benchmarks/systemf-normalization-nondeterminism-hard) | [✔](benchmarks/systemf-normalization-nondeterminism-medium) | [✔](benchmarks/systemf-normalization-nondeterminism-easy) | [✔](benchmarks/systemf-parametricity-nondeterminism-hard) | [✔](benchmarks/systemf-parametricity-nondeterminism-medium) | [✔](benchmarks/systemf-parametricity-nondeterminism-easy) |
| Recursion | [✔](benchmarks/stlc-normalization-recursion-hard) | [✔](benchmarks/stlc-normalization-recursion-medium) | [✔](benchmarks/stlc-normalization-recursion-easy) | [✔](benchmarks/systemf-normalization-recursion-hard) | [✔](benchmarks/systemf-normalization-recursion-medium) | [✔](benchmarks/systemf-normalization-recursion-easy) | [✔](benchmarks/systemf-parametricity-recursion-hard) | [✔](benchmarks/systemf-parametricity-recursion-medium) | [✔](benchmarks/systemf-parametricity-recursion-easy) |
| If-then-else + Non-determinism | [✔](benchmarks/stlc-normalization-if-nondeterminism-hard) | [✔](benchmarks/stlc-normalization-if-nondeterminism-medium) | [✔](benchmarks/stlc-normalization-if-nondeterminism-easy) | [✔](benchmarks/systemf-normalization-if-nondeterminism-hard) | [✔](benchmarks/systemf-normalization-if-nondeterminism-medium) | [✔](benchmarks/systemf-normalization-if-nondeterminism-easy) | [✔](benchmarks/systemf-parametricity-if-nondeterminism-hard) | [✔](benchmarks/systemf-parametricity-if-nondeterminism-medium) | [✔](benchmarks/systemf-parametricity-if-nondeterminism-easy) |
| If-then-else + Recursion | [✔](benchmarks/stlc-normalization-if-recursion-hard) | [✔](benchmarks/stlc-normalization-if-recursion-medium) | [✔](benchmarks/stlc-normalization-if-recursion-easy) | [✔](benchmarks/systemf-normalization-if-recursion-hard) | [✔](benchmarks/systemf-normalization-if-recursion-medium) | [✔](benchmarks/systemf-normalization-if-recursion-easy) | [✔](benchmarks/systemf-parametricity-if-recursion-hard) | [✔](benchmarks/systemf-parametricity-if-recursion-medium) | [✔](benchmarks/systemf-parametricity-if-recursion-easy) |
| Non-determinism + Recursion | [✔](benchmarks/stlc-normalization-nondeterminism-recursion-hard) | [✔](benchmarks/stlc-normalization-nondeterminism-recursion-medium) | [✔](benchmarks/stlc-normalization-nondeterminism-recursion-easy) | [✔](benchmarks/systemf-normalization-nondeterminism-recursion-hard) | [✔](benchmarks/systemf-normalization-nondeterminism-recursion-medium) | [✔](benchmarks/systemf-normalization-nondeterminism-recursion-easy) | [✔](benchmarks/systemf-parametricity-nondeterminism-recursion-hard) | [✔](benchmarks/systemf-parametricity-nondeterminism-recursion-medium) | [✔](benchmarks/systemf-parametricity-nondeterminism-recursion-easy) |
| If-then-else + Non-determinism + Recursion | [✔](benchmarks/stlc-normalization-if-nondeterminism-recursion-hard) | [✔](benchmarks/stlc-normalization-if-nondeterminism-recursion-medium) | [✔](benchmarks/stlc-normalization-if-nondeterminism-recursion-easy) | [✔](benchmarks/systemf-normalization-if-nondeterminism-recursion-hard) | [✔](benchmarks/systemf-normalization-if-nondeterminism-recursion-medium) | [✔](benchmarks/systemf-normalization-if-nondeterminism-recursion-easy) | [✔](benchmarks/systemf-parametricity-if-nondeterminism-recursion-hard) | [✔](benchmarks/systemf-parametricity-if-nondeterminism-recursion-medium) | [✔](benchmarks/systemf-parametricity-if-nondeterminism-recursion-easy) |
