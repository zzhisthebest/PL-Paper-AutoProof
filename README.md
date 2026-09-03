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
| None |  |  |  |  |  |  | [✔](benchmarks/systemf) |  |  |
| If-then-else | [✔](benchmarks/stlc) |  |  |  |  |  |  |  |  |
| Non-determinism |  |  |  |  |  |  |  |  |  |
| Recursion |  |  |  |  |  |  |  |  |  |
| If-then-else + Non-determinism |  |  |  |  |  |  |  |  |  |
| If-then-else + Recursion |  |  |  |  |  |  |  |  |  |
| Non-determinism + Recursion |  |  |  |  |  |  |  |  |  |
| If-then-else + Non-determinism + Recursion |  |  |  |  |  |  |  |  |  |
