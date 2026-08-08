# 用 AI Agent 自动构造 Type Denotation / Logical Relation 的研究想法

## 核心想法

我想做的是：让 AI Agent 自动帮助构造 PL / 程序验证论文中最关键的语义不变量，也就是 type denotation、term denotation、logical relation，甚至包括选择合适的 semantic domain。

目标不是简单让 LLM 写 proof script，而是让它参与“证明为什么类型系统是 sound 的”这一层最核心的设计。

## 1. 问题背景

在 PL 和程序验证论文里，有一大类工作是在设计类型系统。例如 Rust 的类型系统可以保证内存安全。对于简单语言，类型安全通常可以用 progress + preservation 证明。但对于更复杂的类型系统，比如 Rust 的 ownership / borrowing、unsafe abstraction、并发、substructural resource 等，单纯的 syntactic proof 往往不够，通常需要 denotational semantics 或 logical relation。

这类证明里的核心难点是：如何定义一个合适的 type denotation / logical relation。它本质上就像程序验证里的 inductive invariant：

- 定义太弱，无法推出安全性；
- 定义太强，typing rule 无法证明 sound；
- 定义方式不合适，证明会非常复杂，甚至需要引入新的 semantic domain，例如 separation logic、resource algebra、lifetime logic、step-indexed Kripke logical relation 等。

可以参考两篇背景文献：

1. Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. *A Logical Approach to Type Soundness*. JACM 2024.  
   <https://iris-project.org/pdfs/2024-jacm-logical-type-soundness.pdf>

2. John C. Reynolds. *The Meaning of Types: From Intrinsic to Extrinsic Semantics*. BRICS RS-00-32, 2000.  
   <https://www.brics.dk/RS/00/32/BRICS-RS-00-32.pdf>

第一篇论文说明为什么 semantic / logical type soundness 比 progress + preservation 更强，尤其适合解释 abstraction 和 unsafe / safe interaction。第二篇论文提供了 intrinsic / extrinsic semantics 的经典视角：我们可以把类型看成对程序语义的 property / relation，而不是只看 typing derivation 本身。

## 2. 我打算做什么

我希望构建一个 AI Agent 系统，输入包括：

- 一个小语言或类型系统的语法；
- operational semantics；
- typing rules；
- 用户想证明的 soundness theorem；
- 可选的例子、测试、已有 proof attempt。

Agent 的目标是自动构造：

- semantic domain；
- type denotation；
- term denotation；
- logical relation；
- context interpretation；
- typing rule soundness proof obligations；
- 必要时引入 resource algebra、step-indexing、Kripke world、separation logic predicate、prophecy variable 等结构。

大致 workflow 是：

```text
输入语言定义 + typing rules + soundness theorem
        ↓
Agent 提出 candidate semantic domain 和 type denotation
        ↓
尝试证明每条 typing rule 的 semantic soundness
        ↓
如果失败，分析失败原因：
  invariant 太强 / 太弱 / 缺 resource / 缺 monotonicity / semantic domain 不够
        ↓
修改 denotation 或 semantic domain
        ↓
反复迭代，直到 typing rules 可证明
        ↓
进一步检查是否可以推广 typing rules
```

我特别感兴趣的一点是：如果某个 denotation 成功证明了原 typing rules，它可能还允许更强、更自由的 typing rule。这说明原论文里的规则可能过于保守。这个方向不仅能复现已有证明，还可能发现已有类型系统设计中的限制或改进空间。

我觉得 benchmark 可以分成三类：

1. **已有论文本身就有 denotation / logical relation 的情况**  
   这类 benchmark 用来测试 agent 能不能恢复、简化或重新组织已有的人类设计。例如 RustBelt、RustHornBelt、VerusBelt 这类工作中，type denotation / logical relation 本身就是论文的核心贡献。这里的目标不是假装从零发明，而是看 agent 是否能根据 typing rules 和 soundness theorem 找到类似的 invariant，或者发现更简单、更模块化的定义方式。

2. **已有论文有 soundness proof，但没有采用 denotation / logical relation 的情况**  
   例如一些工作可能用 progress + preservation 或其他 syntactic proof 证明 soundness。这类 benchmark 可以测试 agent 是否能把一个 syntactic proof 问题重新解释成 semantic type soundness / logical relation 问题。这样可以验证 agent 不是只会复述原论文，而是真的能提出另一种证明结构。

3. **已有系统没有完整证明，或者只有非形式化证明的情况**  
   这类 benchmark 更接近真实研究场景。输入可能只有语言定义、typing rules、一些例子和目标 theorem。Agent 需要尝试构造 denotation / logical relation。如果成功，就能补全原来缺失的 soundness proof；如果失败，也可能暴露 typing rule 本身不 sound，或者指出缺少必要的语义结构。

这三类 benchmark 的作用不同：第一类用于校准和复现，第二类用于测试证明方法迁移，第三类用于发现新问题或补全已有工作的 proof gap。

除此之外，benchmark 还可以用来观察证明框架本身的局限性。很多已有证明依赖大型库或框架，例如 Iris、separation logic library、step-indexed logical relation library 等。这些框架提供了强大的表达能力，但也可能带来额外负担：某些 denotation 必须绕着框架的接口写，某些概念需要通过复杂的 resource algebra 或 proof pattern 间接表达，导致定义不够直观、proof script 很重，或者可读性较差。

如果 agent 能在同一个 typing rule soundness task 上尝试不同的 semantic domain、不同的 denotation factoring、不同的 proof architecture，我们就可以比较：

- 哪些复杂性来自问题本身；
- 哪些复杂性来自当前证明框架的限制；
- 是否存在更直接、更可读的 denotation；
- 是否需要为这类证明设计新的 library abstraction 或新的 semantic framework。

因此，这个 benchmark 不只是评估 agent 能不能证明定理，也可以反过来帮助我们评估 Iris 等现有框架在表达某类 type denotation / logical relation 时的工程负担，并为提出更好的证明框架提供指导。

## Case Study 设计

Case study 可以从简单到复杂分层：

- STLC / System F / affine lambda calculus：验证 agent 能否恢复基本 logical relation；
- region / ownership calculus：测试 agent 是否能发现 resource-sensitive semantics；
- Rust-like borrowing calculus：测试 agent 是否能发现 `own` / `shr` split、mutable reference 的 current / future model；
- RustBelt / RustHornBelt / VerusBelt 片段：作为最有影响力的复杂案例。

Rust 是很好的 flagship case，因为 Rust 语言很热门，RustBelt 系列工作在 PL 界也很有代表性，而且其证明复杂度正好体现了“type denotation 设计”本身的重要性。

## 3. 为什么这个问题重要

这个问题重要在于，它把 AI for Proof 从“写 tactic”推进到了“发现证明的核心不变量”。

目前很多 AI for Proof 工作集中在：

- 证明单个 lemma；
- 生成 tactic；
- proof repair；
- theorem proving benchmark。

但在 PL / 程序验证里，真正困难的地方经常不是某一步 tactic，而是：

> 我们到底应该定义什么 invariant，才能让整个 soundness proof 成立？

如果这个问题能被 agent 部分自动化，会有几个价值：

1. **帮助设计复杂类型系统**  
   研究者可以更快验证一个 typing rule 是否 sound，也可以探索 alternative denotation。

2. **降低 PL mechanization 门槛**  
   很多论文的形式化证明难点在 denotation / logical relation 设计。如果 agent 能给出候选定义，会极大减轻 proof engineering 成本。

3. **发现已有系统的不足**  
   Agent 可能发现原 denotation 过于复杂，或者原 typing rules 过于保守，甚至指出某些 rule 实际不 sound。

4. **连接数学逻辑和系统验证**  
   这个项目天然结合 logical relation、denotational semantics、substructural logic、separation logic 和程序验证，非常适合作为北大数院与系统 / PL 方向合作的切入点。

5. **RustBelt case study 有影响力**  
   如果能在 RustBelt 风格的 fragment 上展示 agent 自动发现或简化 denotation，会非常有说服力，也容易让 PL 社区关注。

6. **帮助改进现有证明框架**  
   许多复杂 PL soundness proof 依赖 Iris 等大型证明框架。这些框架很强，但也可能让某些 denotation 变得格外复杂。Agent 可以尝试重构这些证明，比较不同 denotation 和 proof architecture，从而发现哪些复杂性是本质的，哪些是框架带来的工程负担。这可能进一步指导我们设计更好的 semantic library、logical relation framework 或 proof harness。
