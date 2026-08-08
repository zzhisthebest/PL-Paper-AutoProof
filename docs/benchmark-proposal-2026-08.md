# 研究计划：用 AI Agent 自动构造 Type Denotation / Logical Relation

**版本**：2026-08-08（沟通稿）
**作者**：周喆（Purdue 大学，2026 年 9 月起北京大学助理教授）
**近期合作**：张子豪（南京大学）——负责 Benchmark 构建
**远期合作**：北京大学数学科学学院（待邀请）

---

## 0. 一句话总结

让 AI Agent 自动构造 PL / 程序验证论文中最关键的**语义不变量**（type denotation、term denotation、logical relation、semantic domain），把 AI for Proof 从"写 tactic"推进到"发现证明的核心不变量"。

本文档把工作拆成两部分：

- **Benchmark（近期，张子豪负责）**：构建"给定语言定义 + 目标定理 → 自动构造语义不变量"的任务集，从类型系统推广到 abstract machine / definitional interpreter / staged evaluator 等更广义的 PL 语义工作；
- **Solution（后续，周喆负责）**：agent 系统原型、证明失败反馈回路、"哪些复杂性来自问题本身、哪些来自证明框架"的比较研究。

Benchmark 先行，既为 Solution 提供数据和评价基准，本身也有独立的学术产出价值。

---

## 1. 背景（2 分钟版）

- 在 PL 与程序验证论文里，一大类工作是在设计类型系统。对简单语言，type soundness 可以用 progress + preservation 证明；但对 Rust 的 ownership / borrowing、unsafe 抽象、并发、substructural resource 等复杂系统，通常需要 denotational semantics 或 logical relation。
- 这类证明的核心难点，是**如何定义合适的 type denotation / logical relation**——它本质上就是程序验证里的 inductive invariant：
  - 定义太弱，推不出安全性；
  - 定义太强，typing rule 证不了；
  - 定义方式不合适，证明会非常复杂，甚至要引入新 semantic domain（separation logic、resource algebra、lifetime logic、step-indexed Kripke logical relation 等）。
- 两篇背景文献：
  1. **Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal.** *A Logical Approach to Type Soundness.* JACM 2024 —— 说明 semantic / logical type soundness 比 progress + preservation 更强，尤其适合 abstraction 与 unsafe / safe 交互。
  2. **John C. Reynolds.** *The Meaning of Types: From Intrinsic to Extrinsic Semantics.* BRICS RS-00-32, 2000 —— intrinsic / extrinsic semantics 的经典视角：类型是对程序语义的 property / relation。
- 现状差距：现有 AI for Proof 工作集中在写 lemma / tactic、proof repair、theorem proving benchmark；而 PL 里真正难的地方是"**到底该定义什么不变量**"，目前基本靠人。

---

## 2. Benchmark：任务定义（张子豪的主线）

### 2.1 统一任务格式（问题卡片）

每个任务用一张**问题卡片**（problem card）描述，尽量机器可读、可复用：

**输入**

- 语言语法（BNF，或已有 Coq / Lean 定义，优先复用现有 artifact）；
- 操作语义（big-step / small-step / abstract machine / definitional interpreter）；
- typing rules，或待验证的目标语义对象；
- 目标定理（type soundness / 抽象解释 soundness / 变换语义保持 / 机器与解释器等价）；
- 可选：例子、测试、已有 proof attempt。

**期望输出**

- semantic domain（或 abstract domain + Galois connection / abstraction relation）；
- type denotation / term denotation / logical relation（或 simulation relation）；
- context interpretation；
- 每条 typing rule（或每个语义步骤）对应的 proof obligation；
- 完整证明脚本（Rocq / Lean），要求无 `Admitted`。

### 2.2 三类任务（类型系统层）

| 类别 | 定义 | 例子 | 研究目的 |
|---|---|---|---|
| 一：复现与简化 | 论文本身已有 denotation / logical relation | RustBelt (POPL'18)、RustHornBelt (POPL'22)、VerusBelt (PLDI'26)、Reachability Types 的 logical relation (OOPSLA'25) | agent 能否根据 typing rules + 目标定理恢复出类似（或更简单、更模块化）的不变量 |
| 二：证明结构迁移 | 论文有 soundness proof，但不是 denotation / LR（多为 progress + preservation） | STLC、System F、Featherweight Java (TOPLAS'01) | agent 能否把 syntactic proof 重铸为 semantic type soundness / LR，而不是复述原论文 |
| 三：补全缺失证明 | 系统没有完整证明，或只有非形式化论证 | 见下节 abstract machine 线 | 成功则补全 soundness proof；失败可能暴露规则不 sound，或缺少必要语义结构 |

### 2.3 推广：超越类型系统（abstract machine 线）

原想法只覆盖类型系统；本项目的一个关键推广是：**把"构造语义不变量"推广到一般的 PL 语义工作**。理由：(1) 任务结构同构——都是"给定形式定义与目标定理，构造让证明成立的语义结构"；(2) 数据更丰富——这些工作大多没有机械化形式化，benchmark 直接产生研究价值。

候选任务（正确性声明多为非形式化论证，未见公开机械化形式化；**"无形式化"这一点需要在建卡片时逐篇核实**）：

| 论文 | 正确性声明 | 要构造的语义结构 |
|---|---|---|
| Van Horn & Might, *Abstracting Abstract Machines* (ICFP'10) | 抽象机上的抽象解释（CFA）相对于具体机器语义 sound | abstract domain + abstraction / simulation relation |
| Johnson & Van Horn, *Abstracting Definitional Interpreters* (ICFP'14) | 统一为 definitional interpreter 后抽象版本仍 sound | monadic abstract interpreter 的 soundness invariant |
| Danvy & Nielsen, *Refocusing in Reduction Semantics* (BRICS RS-04-26, 2004) | refocus 与 plug-then-decompose 结果相同 | 约简语义与抽象机之间的等价 / simulation |
| Danvy & Millikin, *Refunctionalization at Work* (SCP'09) | defunctionalization 的左逆语义保持 | 函数表示与一等函数的语义等价 |
| Wei, Decker & Rompf, *Refunctionalization of Abstract Abstract Machines* (ICFP'18, pearl) | AAM 与 ADI 通过 refunctionalization 相互转换 | 机器状态 ↔ 解释器状态的双向转换保持 soundness |
| Wei, Tan & Zhong, *Let It Be Optimized: Multi-Stage Evaluators with Let-Insertion* (ICFP'26, pearl) | staged evaluator 中 let-insertion 与优化保持语义 | 分阶段求值 / let-insertion 的语义保持不变量 |

说明：最后一篇（ICFP'26 pearl）是该线**最近**的工作，其 related work 展示了完整脉络（MetaML、LMS、staged abstract interpreters 等），可以作为问题卡片书写的文献地图。

### 2.4 任务优先级

| 优先级 | 任务 | 说明 | 类别 |
|---|---|---|---|
| **P0** | STLC logical relation（call-by-value） | 校准：有大量现成 Coq/Lean 参考，验证 agent 管线与评价指标 | 一 |
| **P0** | System F parametricity | 校准：逻辑等价 + 自由定理，验证 agent 处理高阶量词 | 一 |
| **P1** | RustBelt 最小片段（λ_rust 子集，own/shr 模型） | 已有 Iris + Coq 形式化；测试能否恢复 own/shr split、current/future model | 一 |
| **P1** | Reachability Types 片段 | OOPSLA'25 有 logical relation，POPL'24 有 Coq 机械化；测试简化 / 重组织 | 一 |
| **P2** | Featherweight Java 重铸 | 把 syntactic type soundness 重铸为 semantic soundness | 二 |
| **P2** | region / ownership 小语言 | 测试能否发现资源敏感语义 | 二/三 |
| **P3** | AAM / ADI 的 soundness 形式化 | 补全缺失证明（machine 线前两行） | 三 |
| **P3** | Refunctionalization AAM ↔ ADI 等价性 | 补全缺失证明（machine 线第五行） | 三 |
| **P3** | let-insertion 语义保持（ICFP'26 pearl） | 最新、难度最高（machine 线末行） | 三 |

### 2.5 每个 case 的交付物（四件套）

1. **问题卡片**：输入 / 输出 / 目标定理，机器可读（Markdown 或 JSON），附语言定义骨架（Rocq / Lean）；
2. **运行日志**：agent 的 candidate denotation、失败尝试与原因分析、最终结果；
3. **形式化产物**：Rocq / Lean 证明脚本（无 `Admitted`）+ 说明文档；
4. **元数据**：难度、是否已有公开形式化、参考文献、备注（如发现原规则过强 / 过弱）。

### 2.6 建议里程碑

| 时间 | 里程碑 | 内容 |
|---|---|---|
| 第 1–2 周 | M0：跑通管线 | P0 两个校准 case 的问题卡片；用现有 LLM agent（如 Codex）+ Rocq 跑出基线；确定运行记录模板与评价指标 |
| 第 3–6 周 | M1：类型系统层 | P1、P2 共 4–6 个 case；整理"复现 / 迁移 / 补全"三类结果对比 |
| 第 7–12 周 | M2：推广层 | abstract machine 线 2–3 个 case（建议先 AAM，再 refunctionalization，最后 let-insertion）；中期报告 |
| 持续 | 元数据维护 | 逐篇核实候选论文是否有公开形式化，维护 benchmark 清单 |

### 2.7 工具链建议

- **证明助手**：Rocq 9.1 + stdpp（团队有成熟经验，见 `UnderLogicAndType` 项目）；Lean 4 作为对照后端；
- **框架**：Iris / separation logic 仅在对齐原论文时使用（P1 的 RustBelt 片段）；其他 case 鼓励"直接定义"的轻量路线，便于比较框架负担（见 §3.3）；
- **自动化**：coqhammer、lia、eauto、QuickChick（反例搜索）；
- **Agent 基线**：Codex / Claude 等现成 agent，统一 prompt 模板，记录每次运行。

---

## 3. Solution：后续探索方向（周喆）

### 3.1 Agent 系统工作流

```
输入：语言定义 + typing rules + 目标定理
        ↓
Agent 提出 candidate semantic domain 和 type denotation
        ↓
尝试证明每条 typing rule 的 semantic soundness
        ↓
如果失败，分析失败原因：
  不变量太强 / 太弱 / 缺 resource / 缺 monotonicity / semantic domain 不够
        ↓
修改 denotation 或 semantic domain → 迭代
        ↓
收敛后：检查是否可以推广 typing rules（原论文可能过于保守）
```

### 3.2 关键技术挑战

- **候选生成**：把 denotation 的常见结构（product / sum / function / existential / step-indexing / resource algebra / Kripke world）做成小的组合 DSL，让 agent 在此空间内搜索；
- **失败反馈回路**：把证明失败（未闭合目标、循环依赖）转成可操作信号；用 QuickChick / small-model 找反例，区分"denotation 错了"与"证明差一步"；
- **证明后端**：Rocq / Lean 双后端，与 denotation 生成解耦，让失败分析聚焦于不变量设计；
- **评价指标**：成功率之外，度量 denotation 的可读性 / 模块化、是否需要新 domain、能否发现更强 typing rules。

### 3.3 一个重要的科学问题：证明框架的负担

很多已有证明依赖大型框架（Iris、separation logic 库、step-indexed LR 库）。这些框架表达力强，但也可能带来额外负担：某些 denotation 必须绕着框架接口写，导致定义不直观、proof script 很重。

如果 agent 能在同一个 soundness 任务上尝试不同的 semantic domain / denotation factoring / proof architecture，就能系统比较：

- 哪些复杂性来自问题本身，哪些来自框架限制；
- 是否存在更直接、更可读的 denotation；
- 是否需要为这类证明设计新的 library abstraction 或 semantic framework。

因此这个项目不只是评估 agent 能不能证明定理，也能反过来评估 Iris 等框架的工程负担，指导更好的 proof harness 设计。

### 3.4 为什么重要

1. 帮助设计复杂类型系统（快速验证 typing rule 是否 sound）；
2. 降低 PL mechanization 门槛（难点在 denotation / LR 设计）；
3. 发现已有系统不足（denotation 过复杂、rules 过保守、甚至不 sound）；
4. 连接数学逻辑与系统验证（logical relation、denotational semantics、substructural logic、separation logic）；
5. RustBelt 风格 case study 有影响力；
6. 改进现有证明框架（见 §3.3）。

---

## 4. 路线图与分工

| 阶段 | 时间 | 内容 | 负责人 |
|---|---|---|---|
| 阶段 0 | 2026-08 起 | Benchmark 构建：问题卡片、基线运行、元数据 | 张子豪（周喆指导） |
| 阶段 1 | 2026 秋 | Solution 原型 v1：P0/P1 的 denotation 候选生成 + 迭代证明 | 周喆 |
| 阶段 2 | 2027 春 | 推广到 abstract machine 线；框架负担比较实验 | 张子豪 + 周喆 |
| 阶段 3 | 2027 年 | 论文产出：benchmark 报告 / 方法论文；评估与北大数院合作 | 全体 |

### 与北大数院的合作（远期）

该方向为数学侧提供明确的问题来源：logical relation 的模型论、domain theory、substructural logic 与 categorical semantics、step-indexing 与 Kripke 语义。数院可以从理论上刻画"正确 / 最优的 denotation"（例如作为某个 universal property），让 agent 的搜索更有方向，也把"AI 自动构造不变量"做成有数学深度的方向。

---

## 5. 近期待办（给张子豪的第一批任务）

1. 按 §2 完成 P0 两张问题卡片（STLC、System F），并跑通一次 Codex / Rocq 基线；
2. 维护候选论文清单（类型层 + machine 层），逐篇核实是否有公开形式化；
3. 固定运行记录模板与评价指标，保证结果可复现、可比较。

有任何问题（尤其是问题卡片格式、工具链、P0 卡片选择）随时沟通。

---

## 6. 主要参考文献

1. Timany, Krebbers, Dreyer, Birkedal. *A Logical Approach to Type Soundness.* JACM 2024.
2. Reynolds. *The Meaning of Types: From Intrinsic to Extrinsic Semantics.* BRICS RS-00-32, 2000.
3. Wright, Felleisen. *A Syntactic Approach to Type Soundness.* I&C 1994.
4. Jung, Jourdan, Krebbers, Dreyer. *RustBelt: Securing the Foundations of the Rust Programming Language.* POPL 2018.
5. Matsushita, Denis, Jourdan, Dreyer. *RustHornBelt.* POPL 2022.
6. Hance, Elbeheiry, Matsushita, Dreyer. *VerusBelt.* PLDI 2026.
7. Jung et al. *Iris from the Ground Up.* JFP 2018.
8. Bao, Jia, Wei, Bračevac, Rompf. *Modeling Reachability Types with Logical Relations.* OOPSLA 2025.
9. Van Horn, Might. *Abstracting Abstract Machines.* ICFP 2010.
10. Johnson, Van Horn. *Abstracting Definitional Interpreters.* ICFP 2014.
11. Danvy, Nielsen. *Refocusing in Reduction Semantics.* BRICS RS-04-26, 2004.
12. Danvy, Millikin. *Refunctionalization at Work.* SCP 2009.
13. Wei, Decker, Rompf. *Refunctionalization of Abstract Abstract Machines (Functional Pearl).* ICFP 2018.
14. Wei, Tan, Zhong. *Let It Be Optimized: Building Multi-Stage Evaluators with Let-Insertion and Optimizations in Small Pieces (Functional Pearl).* ICFP 2026.
15. Igarashi, Pierce, Wadler. *Featherweight Java.* TOPLAS 2001.
