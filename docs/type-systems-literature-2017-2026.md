# Type Systems 文献检索：2017–2026

按发表年份覆盖 2017–2026。**155 篇论文：116 篇找到公开的 Coq/Rocq 形式化入口，39 篇暂列其他线索。** 形式化入口包括作者仓库、归档或论文附录链接；未逐篇编译，也没有判断可抽成多少独立 benchmark 题。一个项目的多篇论文先分别保留，同篇论文的 arXiv、会议版、期刊增补版不重复计数。

检索从 [PACMPL 逐期目录](https://ftp.math.utah.edu/pub/tex/bib/toc/pacmpl.html)、[SIGPLAN OpenTOC](https://sigplan.org/OpenTOC/) 和 ECOOP、FSCD、ITP、ESOP 等论文或 artifact 目录出发，再查 LICS、FoSSaCS、TYPES 及 JFP、LMCS、MSCS、TOPLAS、JAR 等期刊目录或条目。也按定理关键词（如 normalization、coherence、conversion、interpolation）补搜，并通过论文参考文献和作者主页定位对应代码。只实现了类型检查器、或虽然改了 Coq 内核但用 Agda 写元理论证明的，不计入 Rocq 入口。并非十年所有 venue 的逐篇全文检索。

收录范围是类型系统与其元理论：终止性、参数性、类型安全、信息流、类型推断、conversion 等。证明某个算法实例或某份代码满足规格不算；编译管线单独排除。类型检查算法可保留为线索，但证明它正确不一定需要重新设计 LR。少数项目如 GhostCell 偏类型化接口，保留供下一轮判断。

与现有 5 道题最接近的一组（不是最终 shortlist）：

- [Towards Strong Normalization for Dependent Object Types (DOT)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2017.27)：研究 DOT 子演算的强规范化，不等于完整 DOT 的 SN。
- [Modeling Reachability Types with Logical Relations: Semantic Type Soundness, Termination, Effect Safety, and Equational Theory](https://bracevac.org/assets/pdf/oopsla25b.pdf)：用 LR 证明 semantic type soundness 或 termination。
- [Mechanizing Refinement Types](https://arxiv.org/abs/2207.05617)：λRF 的类型安全与 denotational soundness；artifact 同时有 Coq 与 LiquidHaskell。
- [Backwards-Compatible Row-Based Exceptions in ML](https://pldi26.sigplan.org/details/pldi-2026-papers/60/Backwards-Compatible-Row-Based-Exceptions-in-ML)：row-based exception typing 的 logical relation。
- [Mechanized Logical Relations for Termination-Insensitive Noninterference](https://iris-project.org/pdfs/2021-popl-tiniris-final.pdf)：使用 LR 证明 termination-insensitive noninterference。
- [Semantics for Noninterference with Interaction Trees](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.29)：第 5 节从 Imp 的类型规则推导 noninterference；第 6 节是编译器定理，不纳入这一类。
- [Formalizing, Mechanizing, and Verifying Class-Based Refinement Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.39)：把现有的 refinement type safety 方向扩展到了类式语言。

## 找到 Coq/Rocq 形式化入口

### 多态与元理论（19）

| 论文 | 公开代码 / artifact | 研究的问题 |
| --- | --- | --- |
| [Bidirectional Interpolation for the λ-Calculus: Revisiting and Formalising Craig-Čubrić Interpolation](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.30) · ITP 2026 | [入口](https://github.com/MevenBertrand/interpolation) | 带 sum types 的 STLC 中，用 bidirectional typing 证明 proof-relevant interpolation；归档说明将部分 commuting-conversion confluence 单列为公理 |
| [Formal P-Category Theory and Normalization by Evaluation in Rocq](https://doi.org/10.1017/S0960129525100406) · MSCS 2026 | [作者归档](https://doi.org/10.17863/CAM.124568) | STLC 的 categorical normalization by evaluation 正确性；归档是作者配套学位论文的代码，尚未逐文件核对期刊版 |
| [Mechanised Semantics of Multi-Stage Programming](https://xnning.github.io/papers/oopsla26mechanised.pdf) · OOPSLA 2026 | [入口](https://zenodo.org/records/18307307) | 多阶段语言的类型性质；具体入选目标待定 |
| [Typing Strictness](https://arxiv.org/abs/2510.16133) · POPL 2026 | [入口](https://github.com/plclub/typing-strictness) | 类型系统给出的 strictness 保证 |
| [A Logical Approach to Type Soundness](https://cs.au.dk/~timany/publications/pub_pages/2024-logical-type-soundness-jacm/) · JACM 2024 | [入口](https://github.com/tchajed/iris-simp-lang/) | semantic type soundness 与 representation independence；链接是论文所指的配套教学源码，覆盖范围待确认 |
| [Mechanizing Refinement Types](https://arxiv.org/abs/2207.05617) · POPL 2024 | [入口](https://zenodo.org/records/8425960) | λRF 的类型安全与 denotational soundness；artifact 同时有 Coq 与 LiquidHaskell |
| [RichWasm: Bringing Safe, Fine-Grained, Shared-Memory Interoperability Down to WebAssembly](https://arxiv.org/abs/2401.08287) · PLDI 2024 | [入口](https://github.com/RichWasm/RichWasm-artifact) | 具有资源与共享内存的 Wasm 类型系统的安全性 |
| [The Essence of Generalized Algebraic Data Types](https://iris-project.org/pdfs/2024-popl-gadt.pdf) · POPL 2024 | [入口](https://zenodo.org/records/10040534) | GADT 的关系语义与抽象 |
| [Formalizing, Mechanizing, and Verifying Class-Based Refinement Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.39) · ECOOP 2024 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.10.2.22) | 带精化类型的类式演算 RFJ 的 soundness |
| [Two Mechanisations of WebAssembly 1.0](https://vtss.doc.ic.ac.uk/publications/Watt2021Two.html) · FM 2021 | [入口](https://github.com/WasmCert/WasmCert-Coq) | 只收 Wasm 1.0 类型安全或算法式 typing 的定理，不收解释器和编译任务 |
| [Scala Step-by-Step: Soundness for DOT with Step-Indexed Logical Relations in Iris](https://iris-project.org/pdfs/2020-icfp-dot-final.pdf) · ICFP 2020 | [入口](https://github.com/Blaisorblade/dot-iris) | gDOT 的 semantic type soundness |
| [A Path to DOT: Formalizing Fully Path-Dependent Types](https://arxiv.org/abs/1904.07298) · OOPSLA 2019 | [入口](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths) | 加入任意路径后的 DOT 类型安全 |
| [POPLMark Reloaded: Mechanizing Proofs by Logical Relations](https://doi.org/10.1017/S0956796819000170) · JFP 2019 | [入口](https://poplmark-reloaded.github.io/) | STLC 的 logical-relations 证明；这是已有 benchmark，适合作为对照，不宜直接算作全新的研究题 |
| [Call-by-Push-Value in Coq: Operational, Equational, and Denotational Theory](https://doi.org/10.1145/3293880.3294097) · CPP 2019 | [入口](https://www.ps.uni-saarland.de/extras/cbpv-in-coq/) | CBPV 类型化演算的语义、指称模型与等式理论；只选原文确实机器检查的定理 |
| [A Simple Soundness Proof for Dependent Object Types](https://arxiv.org/abs/1706.03814) · OOPSLA 2017 | [入口](https://github.com/amaurremi/dot-calculus/tree/master/src/simple-proof) | DOT 的 syntactic soundness |
| [ιDOT: A DOT Calculus with Object Initialization](https://doi.org/10.1145/3428276) · OOPSLA 2020 | [作者代码](https://github.com/themaplelab/dot-public/tree/8f0eaf111f721da0c2b27b1e1935f0128eabc4ef/idot/idot-base/src) | 用 initialization 和 effect 系统约束还没完全初始化的对象；证明类型及初始化安全 |
| [Relating System F and λ2: A Case Study in Coq, Abella and Beluga](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.21) · FSCD 2017 | [入口](https://www.ps.uni-saarland.de/extras/fscd17/sysf_pts.zip) | System F 与 PTS 形式的对应，使用 Coq 的那份 |
| [Towards Strong Normalization for Dependent Object Types (DOT)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2017.27) · ECOOP 2017 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.3.2.5) | 研究 DOT 子演算的强规范化，不等于完整 DOT 的 SN |
| [Type Soundness Proofs with Definitional Interpreters](https://doi.org/10.1145/3009837.3009866) · POPL 2017 | [入口](https://github.com/TiarkRompf/minidot/tree/master/popl17) | 从 System F 到 DOT 的解释器类型安全 |

### 递归、子类型与交并类型（25）

| 论文 | 公开代码 / artifact | 研究的问题 |
| --- | --- | --- |
| [The Logic of Intersection Subtyping](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.62) · LICS 2026 | [入口](https://github.com/olaure01/islogic/tree/LICS2026) | 交类型子类型关系的逻辑刻画及 proof-search 算法的可靠性和完备性；论文附录直接对照 Rocq 定理 |
| [Liberating Merges via Apartness and Guarded Subtyping](https://doi.org/10.1145/3763057) · OOPSLA 2025 | [入口](https://zenodo.org/records/16921686) | 用 type apartness 和 guarded subtyping 给 merge 演算建立类型安全和确定性 |
| [Bidirectional Higher-Rank Polymorphism with Intersection and Union Types](https://doi.org/10.1145/3704907) · POPL 2025 | [入口](https://zenodo.org/records/13922447) | higher-rank polymorphism + 交并类型的推断性质 |
| [Qualified Types with Boolean Algebras](https://plg.uwaterloo.ca/~olhotak/pubs/oopsla25.pdf) · OOPSLA 2025 | [入口](https://github.com/e45lee/artifact-boolean-algebras) | 布尔 qualifier 的子类型和类型性质 |
| [QuickSub: Efficient Iso-Recursive Subtyping](https://ltzhou.com/static/POPL25.pdf) · POPL 2025 | [入口](https://github.com/ltzone/QuickSub) | subtyping 算法的 soundness / completeness |
| [Mechanized Subject Expansion in Uniform Intersection Types for Perpetual Reductions](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2024.8) · FSCD 2024 | [入口](https://github.com/tudo-seal/uniform-intersection) | 论文借 uniform intersection types 给出另一条 STLC 强规范化证明；明确用 Coq 证明的是两套类型系统的 typability 等价 |
| [Full Iso-Recursive Types](https://arxiv.org/abs/2407.00941) · OOPSLA 2024 | [入口](https://github.com/ltzone/Full-Iso-Recursive-Types) | cast soundness 与递归类型等价 |
| [Imperative Compositional Programming: Type Sound Distributive Intersection Subtyping with References via Bidirectional Typing](https://yzsun.me/files/ICP-paper.pdf) · OOPSLA 2024 | [入口](https://zenodo.org/records/13373228) | mutable references 与交类型 |
| [A Case for First-Class Environments](https://doi.org/10.1145/3689800) · OOPSLA 2024 | [入口](https://zenodo.org/records/13370814) | 一等环境的类型元理论；与 ECOOP 2023 同系列，需检查可抽目标是否独立 |
| [Recursive Subtyping for All](https://ltzhou.com/static/POPL23.pdf) · POPL 2023 | [入口](https://github.com/juda/Recursive-Subtyping-for-All) | bounded polymorphism 与 recursive subtyping；2025 JFP 扩展版不另算 |
| [Dependent Merges and First-Class Environments](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.34) · ECOOP 2023 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.9.2.2) | 含一等环境及其运算的演算元理论 |
| [Applicative Intersection Types](https://xnning.github.io/papers/aplas2022applicative.pdf) · APLAS 2022 | [入口](https://zenodo.org/records/7053382) | intersection、overloading 与类型安全 |
| [Direct Foundations for Compositional Programming](https://arxiv.org/abs/2205.06150) · ECOOP 2022 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.8.2.4) | 交类型程序的 type-directed semantics 与类型性质 |
| [Revisiting Iso-Recursive Subtyping](https://hub.hku.hk/handle/10722/322366) · TOPLAS 2022 | [入口](https://github.com/juda/Iso-Recursive-Subtyping) | 递归子类型与 unfolding |
| [Union Types with Disjoint Switches](https://xnning.github.io/papers/ecoop22switches.pdf) · ECOOP 2022 | [入口](https://github.com/baberrehman/disjoint-switches) | union types、分支判别与类型性质 |
| [Row and Bounded Polymorphism via Disjoint Polymorphism](https://xnning.github.io/papers/ecoop20row.pdf) · ECOOP 2020 | [入口](https://github.com/xnning/Row-and-Bounded-via-Disjoint) | 多态编码与类型规则 |
| [The Duality of Subtyping](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2020.29) · ECOOP 2020 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.6.2.8) | subtyping / supertyping 的对偶，覆盖 union 和 intersection |
| [Decidable Subtyping for Path Dependent Types](https://popl20.sigplan.org/details/POPL-2020-Research-Papers/64/Decidable-Subtyping-for-Path-Dependent-Types) · POPL 2020 | [入口](https://github.com/JulianMackay/Wyvern_Formalism) | Wyvself 与 Wyvfix 的子类型可判定性 |
| [Resolution as Intersection Subtyping via Modus Ponens](https://arxiv.org/abs/2010.06216) · OOPSLA 2020 | [入口](https://zenodo.org/records/4043646) | 带 modus ponens 的交类型子类型关系；Coq 对 coherence 只覆盖论文所述部分 |
| [A Type-Directed Operational Semantics for a Calculus with a Merge Operator](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2020.26) · ECOOP 2020 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.6.2.9) | merge 演算的类型可靠性与 type-directed semantics |
| [Distributive Disjoint Polymorphism for Compositional Programming](https://xnning.github.io/papers/distributive-disjoint-polymorphism.pdf) · ESOP 2019 | [入口](https://github.com/bixuanzju/ESOP2019-artifact) | distributive intersection、disjoint polymorphism 与 coherence |
| [The Essence of Nested Composition](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2018.22) · ECOOP 2018 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.4.3.5) | 嵌套组合使用的 record / intersection 类型系统，含 elaboration 的语义性质 |
| [Empowering Union and Intersection Types with Integrated Subtyping](https://doi.org/10.1145/3276482) · OOPSLA 2018 | [入口](https://www.cs.cornell.edu/~ross/publications/empower/empower-oopsla18-artifact.zip) | 集成交并类型的算法式子类型关系可靠且完备 |
| [Disjoint Polymorphism](https://i.cs.hku.hk/~bruno/papers/ESOP2017.pdf) · ESOP 2017 | [入口](https://github.com/jalpuim/disjoint-polymorphism) | disjoint polymorphism 的 coherence 与 type safety；检查原形式化的辅助假设 |
| [Unifying Typing and Subtyping](https://doi.org/10.1145/3133871) · OOPSLA 2017 | [入口](https://bitbucket.org/ypyang/oopsla17) | 把 typing 与 subtyping 合为一种判断；Coq 不覆盖原文对 System F<: 的完备性结论 |

### 类型推断与依赖类型（23）

| 论文 | 公开代码 / artifact | 研究的问题 |
| --- | --- | --- |
| [A Specification for Dependent Types in Haskell](https://doi.org/10.1145/3110275) · ICFP 2017 | [ICFP 2017 版本](https://github.com/sweirich/corespec/tree/edb4931588aee94482454d263558ff3ac970202d/src/FcEtt) | 显式 coercion 的依赖类型核心演算、类型安全，以及显式与隐式系统之间的 erasure / annotation |
| [A Role for Dependent Types in Haskell](https://doi.org/10.1145/3341705) · ICFP 2019 | [ICFP 2019 artifact](https://github.com/sweirich/corespec/tree/icfp19-art/src/FcEtt) | 证明带 dependent types、nominal/representational 等式和 zero-cost coercions 的 System DR 类型安全 |
| [Definitional Proof Irrelevance Made Accessible](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.41) · LICS 2026 | [入口](https://github.com/thiagofelicissimo/acc-in-sprop) | 为 proof-irrelevant 的 accessibility 加入计算规则，用 LR 证明 canonicity |
| [A Sound Pure Type System with Ranks as Sorts and Type-in-Type](https://arxiv.org/abs/2610.25085) · arXiv 2026 | [入口](https://github.com/TurtlePU/pts-rk) | 带自包含 sort 的 pure type system；论文说明其基础 normalization 证明用 Rocq 完成 |
| [Algorithmic Conversion with Surjective Pairing: A Syntactic and Untyped Approach](https://doi.org/10.1145/3776672) · POPL 2026 | [入口](https://doi.org/10.5281/zenodo.17343517) | 带函数和 pair η-laws 的依赖类型 conversion；论文报告全部结果均已在 Rocq 中证明 |
| [Local Contextual Type Inference](https://i.cs.hku.hk/~bruno/papers/popl26.pdf) · POPL 2026 | [入口](https://github.com/juniorxxue/LCTI/tree/main/mech/rocq) | Rocq 只覆盖算法的可判定性；soundness / completeness 在 Agda 中 |
| [McTT: A Verified Kernel for a Proof Assistant](https://doi.org/10.1145/3747511) · ICFP 2025 | [入口](https://zenodo.org/records/15636531) | 聚焦 Martin-Löf type theory 的 normalization 和 typing 算法的 soundness / completeness，不把 parser 等工程部分作为题目 |
| [Consistency of a Dependent Calculus of Indistinguishability](https://www.cis.upenn.edu/~sweirich/papers/popl25.pdf) · POPL 2025 | [入口](https://zenodo.org/records/14252132) | 依赖演算的一致性、normalization 与 conversion；与前作的目标不同 |
| [Practical Type Inference with Levels](https://xnning.github.io/papers/pldi25level.pdf) · PLDI 2025 | [入口](https://zenodo.org/records/15334601) | 基于 levels 的 ML 类型推断 |
| [What Does It Take to Certify a Conversion Checker?](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2025.27) · FSCD 2025 | [入口](https://github.com/CoqHott/logrel-coq/tree/fscd25) | untyped conversion checker；与 CPP 2024 共用仓库，后续检查目标重叠 |
| [Martin-Löf à la Coq](https://arxiv.org/abs/2310.06376) · CPP 2024 | [入口](https://zenodo.org/records/8367154) | 依赖类型的逻辑关系、conversion 和 type checking 的可判定性 |
| [Type Inference Logics](https://2024.splashcon.org/details/splash-2024-oopsla/129/Type-Inference-Logics) · OOPSLA 2024 | [入口](https://github.com/decrn/tilogics) | 算法式与声明式 typing / elaboration 等价 |
| [Definitional Functoriality for Dependent (Sub)Types](https://link.springer.com/chapter/10.1007/978-3-031-57262-3_13) · ESOP 2024 | [入口](https://zenodo.org/records/10461809) | 扩展依赖类型论的 normalization、canonicity 与 type checking；只算 Coq 覆盖的子集 |
| [No Unification Variable Left Behind: Fully Grounding Type Inference for the HDM System](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2023.8) · ITP 2023 | [入口](https://github.com/rogerbosman/hdm-fully-grounding) | 对表达式树求出完整类型信息的 Hindley–Damas–Milner 算法 soundness 和 completeness |
| [Bicategorical Type Theory: Semantics and Syntax](https://doi.org/10.1017/S0960129523000312) · MSCS 2023 | [入口](https://github.com/UniMath/UniMath/commit/840ac16608d642606e6ac4d6eab47fb2507a5256) | 类型论的双范畴语义；Coq 检查的是第 3–7 节的语义结果，不把后续导出的全部句法规则也算成已形式化 |
| [Complete Bidirectional Typing for the Calculus of Inductive Constructions](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.24) · ITP 2021 | [入口](https://github.com/MetaRocq/metarocq) | CIC 双向 typing 的完备性；采用论文对应快照 |
| [A Dependently Typed Calculus with Polymorphic Subtyping](https://doi.org/10.1016/j.scico.2021.102655) · SCP 2021 | [作者源码](https://github.com/VinaLx/dependent-polymorphic-subtyping) | 带隐式多态与显式 cast 的依赖类型；统一子类型关系的类型安全与 transitivity |
| [The Taming of the Rew: A Type Theory with Computational Assumptions](https://popl21.sigplan.org/details/POPL-2021-research-papers/60/The-Taming-of-the-Rew-A-Type-Theory-with-Computational-Assumptions) · POPL 2021 | [入口](https://github.com/TheoWinterhalter/template-coq/tree/rewrite-rules) | 加入计算重写规则后的类型理论；Coq 覆盖部分核心定理，不把一致性算作已形式化 |
| [Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq](https://popl20.sigplan.org/details/POPL-2020-Research-Papers/36/Coq-Coq-Correct-Verification-of-Type-Checking-and-Erasure-for-Coq-in-Coq) · POPL 2020 | [入口](https://zenodo.org/records/3544373) | 选 PCUIC 的类型检查部分，不选 extraction |
| [Eliminating Reflection from Type Theory](https://popl19.sigplan.org/details/CPP-2019/5/Eliminating-Reflection-from-Type-Theory) · CPP 2019 | [入口](https://github.com/TheoWinterhalter/ett-to-itt) | 带 equality reflection 的依赖类型推导可翻译到无反射系统；目标是类型理论本身 |
| [Pure Iso-Type Systems](https://doi.org/10.1017/S0956796819000108) · JFP 2019 | [作者源码](https://bitbucket.org/ypyang/pits-jfp/src/6562c9de3d9c/) | 带一般递归与显式 cast 的依赖类型；类型检查判定性和擦除类型安全 |
| [A Coq Formalization of Normalization by Evaluation for Martin-Löf Type Theory](https://ii.uni.wroc.pl/~dabi/publications/CPP18/wieczorek-biernacki-cpp18.pdf) · CPP 2018 | [入口](https://bitbucket.org/pl-uwr/nbe-martinlof) | 用 PER model 和 LR 证明 NbE 的性质 |
| [Let Arguments Go First](https://xnning.github.io/papers/let-arguments-go-first.pdf) · ESOP 2018 | [入口](https://bitbucket.org/ningningxie/let-arguments-go-first/src/master/) | 高阶多态程序的参数驱动推断 |

### Effect、线性与模态（11）

| 论文 | 公开代码 / artifact | 研究的问题 |
| --- | --- | --- |
| [Backwards-Compatible Row-Based Exceptions in ML](https://pldi26.sigplan.org/details/pldi-2026-papers/60/Backwards-Compatible-Row-Based-Exceptions-in-ML) · PLDI 2026 | [入口](https://zenodo.org/records/19494181) | row-based exception typing 的 logical relation |
| [Mode Crossing](https://iris-project.org/pdfs/2026-icfp-modecrossing.pdf) · ICFP 2026 | [入口](https://zenodo.org/records/21129587) | mode crossing 的语义可靠性；artifact 同时包含实现与形式化内容，待定位目标 |
| [TypeDis: A Type System for Disentanglement](https://iris-project.org/pdfs/2026-popl-typedis.pdf) · POPL 2026 | [入口](https://github.com/nobrakal/typedis) | 并行类型规则的 disentanglement 保证 |
| [Affect: An Affine Type and Effect System](https://iris-project.org/pdfs/2025-popl-affect.pdf) · POPL 2025 | [入口](https://github.com/ovanr/affect) | affine 程序与 effect handler 的类型可靠性 |
| [Data Race Freedom à la Mode](https://iris-project.org/pdfs/2025-popl-drfcaml.pdf) · POPL 2025 | [入口](https://zenodo.org/records/13933463) | OCaml mode system 如何保证 data-race freedom |
| [Effects and Coeffects in Call-by-Push-Value](https://arxiv.org/abs/2311.11795) · OOPSLA 2024 | [入口](https://github.com/plclub/cbpv-effects-coeffects) | CBPV 中同时跟踪 effects 与 coeffects 的 typing / 执行性质 |
| [A Type System for Effect Handlers and Dynamic Labels](https://link.springer.com/chapter/10.1007/978-3-031-30044-8_9) · ESOP 2023 | [入口](https://gitlab.inria.fr/cambium/tes) | 良类型程序不会执行未处理的 effect |
| [A Graded Dependent Type System with a Usage-Aware Semantics](https://doi.org/10.1145/3434331) · POPL 2021 | [入口](https://github.com/sweirich/graded-haskell) | 证明 graded dependent typing 对使用次数语义可靠；definitional equality 的一致性是其假设 |
| [Logical Relations for Coherence of Effect Subtyping](https://doi.org/10.23638/lmcs-14(1:11)2018) · LMCS 2018 | [入口](https://ii.uni.wroc.pl/~ppolesiuk/lrcoherence/) | 用 LR 证明 effect subtyping 与隐式 coercion 的 coherence |
| [A Logical Relation for Monadic Encapsulation of State: Proving Contextual Equivalences in the Presence of runST](https://doi.org/10.1145/3158152) · POPL 2018 | [入口](https://iris-project.org/artifacts/2018-popl-runst.tar.gz) | 带 `runST` 的多态演算中，用 LR 证明状态封装保证；考虑语言级定理，不把单独的程序等价例子当题 |
| [Handle with Care: Relational Interpretation of Algebraic Effects and Handlers](https://ii.uni.wroc.pl/~dabi/publications/POPL18/biernacki-al-popl18.pdf) · POPL 2018 | [入口](https://bitbucket.org/pl-uwr/aleff-logrel) | algebraic effects 与 handlers 的关系解释；论文指向 Coq 源码 |

### ownership、借用与 reachability（14）

| 论文 | 公开代码 / artifact | 研究的问题 |
| --- | --- | --- |
| [Transitive, Abstract, and Class Polymorphic Immutability](https://doi.org/10.1145/3839491) · OOPSLA 2026 | [作者源码](https://github.com/aosen-xiong/pico-rocq) | PICO 的类型安全、mutation safety 和状态保持 |
| [VerusBelt: A Semantic Foundation for Verus’s Proof-Oriented Extensions to the Rust Type System](https://iris-project.org/pdfs/2026-pldi-verusbelt.pdf) · PLDI 2026 | [入口](https://zenodo.org/records/19613067) | Verus 扩展 Rust 类型系统的语义可靠性 |
| [When Lifetimes Liberate: A Type System for Arenas with Higher-Order Reachability Tracking](https://github.com/TiarkRompf/reachability#references) · OOPSLA 2026 | [入口](https://github.com/TiarkRompf/reachability/tree/main/arena) | arena 失效与 scoped deallocation 保证 |
| [Complete the Cycle: Reachability Types with Expressive Cyclic References](https://sweetsinpackets.github.io/file/cycle-paper.pdf) · OOPSLA 2025 | [入口](https://github.com/TiarkRompf/reachability/tree/main/cycles) | 允许循环引用后的类型性质 |
| [Modeling Reachability Types with Logical Relations: Semantic Type Soundness, Termination, Effect Safety, and Equational Theory](https://bracevac.org/assets/pdf/oopsla25b.pdf) · OOPSLA 2025 | [入口](https://github.com/TiarkRompf/reachability/tree/main/log-rel-step-indexed) | 用 LR 证明 semantic type soundness 或 termination |
| [Polymorphic Reachability Types: Tracking Freshness, Aliasing, and Separation in Higher-Order Generic Programs](https://popl24.sigplan.org/details/POPL-2024-popl-research-papers/16/Polymorphic-Reachability-Types-Tracking-Freshness-Aliasing-and-Separation-in-Highe) · POPL 2024 | [入口](https://github.com/TiarkRompf/reachability/tree/main/polymorphism) | 带 reachability qualifiers 的多态类型规则 |
| [RefinedRust: A Type System for High-Assurance Verification of Rust Programs](https://pldi24.sigplan.org/details/pldi-2024-papers/46/RefinedRust-A-Type-System-for-High-Assurance-Verification-of-Rust-Programs) · PLDI 2024 | [入口](https://zenodo.org/records/10912439) | Rust 的 ownership 与 refinement typing 规则 |
| [RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code](https://www.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf) · PLDI 2022 | [入口](https://zenodo.org/records/6426048) | prophecy 与 Rust 模块的 semantic typing |
| [GhostCell: Separating Permissions from Data in Rust](https://plv.mpi-sws.org/rustbelt/ghostcell/paper.pdf) · ICFP 2021 | [入口](https://plv.mpi-sws.org/rustbelt/ghostcell/) | 以类型约束品牌与借用；偏库接口的边界候选 |
| [What If We Don't Pop the Stack? The Return of 2nd-Class Values](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.15) · ECOOP 2022 | [作者代码](https://github.com/angelogeb/scala-native/tree/f0d1e7e1dc5171c0a62bbc07b88bd9c92e34050c/coq) | 用类型区分栈上值；带检查的解释器类型可靠，延迟回收栈帧不改变解释结果 |
| [Reachability Types: Tracking Aliasing and Separation in Higher-Order Functional Programs](https://www.cs.purdue.edu/homes/rompf/papers/bao-oopsla21.pdf) · OOPSLA 2021 | [入口](https://github.com/TiarkRompf/reachability/tree/main/base) | 别名与分离保证 |
| [RefinedC: Automating the Foundational Verification of C Code with Refined Ownership Types](https://plv.mpi-sws.org/refinedc/paper.pdf) · PLDI 2021 | [入口](https://gitlab.mpi-sws.org/iris/refinedc) | refinement typing 与 ownership；考规则可靠性，不考具体验证示例 |
| [RustBelt Meets Relaxed Memory](https://plv.mpi-sws.org/rustbelt/rbrlx/) · POPL 2020 | [入口](https://zenodo.org/records/3539237) | 把 RustBelt 的证明扩展到 relaxed memory；区分语言级结果与库验证 |
| [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/) · POPL 2018 | [入口](https://plv.mpi-sws.org/rustbelt/popl18/) | Rust ownership、borrowing 与 unsafe 抽象的 semantic soundness |

### Session types 与并发类型（9）

| 论文 | 公开代码 / artifact | 研究的问题 |
| --- | --- | --- |
| [Formally Verified Liveness with Multiparty Session Types in Rocq](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.4) · ITP 2026 | [入口](https://github.com/omerskeskin/mpstlive) | 同步多方会话类型的 liveness；用 coinduction 处理 global/local types、projection 和 subtyping |
| [Formalising Subject Reduction and Progress for Multiparty Session Processes](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.19) · ITP 2025 | [入口](https://github.com/Apiros3/smpst-sr-smer) | 同步 MPST 的 non-stuck theorem |
| [Multiparty Asynchronous Session Types: A Mechanised Proof of Subject Reduction](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2025.31) · ECOOP 2025 | [入口](https://github.com/Tirore96/subject_reduction/tree/ECOOP2025/theories) | 异步 MPST 的 subject reduction |
| [Completeness of Asynchronous Session Tree Subtyping in Coq](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.13) · ITP 2024 | [入口](https://github.com/ekiciburak/sessionTreeST/tree/itp2024) | 异步 session tree subtyping 完备性 |
| [A Sound and Complete Projection for Global Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2023.28) · ITP 2023 | [入口](https://github.com/Tirore96/projection) | global session type 投影 soundness / completeness |
| [Higher-Order Leak and Deadlock Free Locks](https://julesjacobs.com/papers/locks/) · POPL 2023 | [入口](https://github.com/julesjacobs/cgraphs) | sharing topology 类型规则保证无死锁 / 无泄漏 |
| [A Self-Dual Distillation of Session Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.23) · ECOOP 2022 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.8.2.15) | session calculus 的类型性质 |
| [Multiparty GV: Functional Multiparty Session Types with Certified Deadlock Freedom](https://iris-project.org/pdfs/2022-icfp-multiparty.pdf) · ICFP 2022 | [入口](https://zenodo.org/records/6882808) | 良类型多方会话的 deadlock freedom |
| [Machine-Checked Semantic Session Typing](https://iris-project.org/pdfs/2021-cpp-sessions-final.pdf) · CPP 2021 | [入口](https://gitlab.mpi-sws.org/iris/actris) | semantic session typing；关注类型规则而非协议程序实例 |

### 渐进类型与信息流（14）

| 论文 | 公开代码 / artifact | 研究的问题 |
| --- | --- | --- |
| [Behavioural Up/down Casting for Statically Typed Languages](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.5) · ECOOP 2024 | [入口](https://zenodo.org/records/7712822) | 静态类型语言中带行为的 cast 及类型安全 |
| [Merging Gradual Typing](https://doi.org/10.1145/3689734) · OOPSLA 2024 | [入口](https://zenodo.org/records/13378311) | gradual typing 与 merge；Coq artifact 不包含动态 gradual guarantee 的证明 |
| [Internalizing Indistinguishability with Dependent Types](https://doi.org/10.1145/3632886) · POPL 2024 | [作者源码](https://electriclam.com/files/dcoi.tar.zst) | 带 observer-indexed equality 的依赖类型；类型安全与 noninterference |
| [Pragmatic Gradual Polymorphism with References](https://link.springer.com/chapter/10.1007/978-3-031-30044-8_6) · ESOP 2023 | [入口](https://link.springer.com/chapter/10.1007/978-3-031-30044-8_6#Sec17) | 有引用的渐进多态语言；soundness、refined gradual guarantee |
| [Semantics for Noninterference with Interaction Trees](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.29) · ECOOP 2023 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.9.2.6) | 选第 5 节 Imp 的两套信息流类型规则与 Theorem 23；不选后面的编译保持 |
| [A Dependent Dependency Calculus](https://link.springer.com/chapter/10.1007/978-3-030-99336-8_15) · ESOP 2022 | [入口](https://github.com/sweirich/graded-haskell/tree/main/DDC) | 依赖类型中分级变量的类型安全与 noninterference |
| [Oblivious Algebraic Data Types](https://doi.org/10.1145/3498713) · POPL 2022 | [作者 artifact](https://ccyip.github.io/oadt/popl22.html) | 带 oblivious data 的依赖类型演算；类型安全与轨迹不可区分性 |
| [A Reasonably Gradual Type Theory](https://arxiv.org/abs/2209.00975) · ICFP 2022 | [入口](https://zenodo.org/records/6928465) | 渐进依赖类型；只统计 Coq 形式化的模型，Agda 原型不是同一对象 |
| [Fully Abstract from Static to Gradual](https://iris-project.org/pdfs/2021-popl-fae-gradual-final.pdf) · POPL 2021 | [入口](https://github.com/scaup/fae-gtlc-mu) | 静态类型到渐进类型嵌入的 full abstraction |
| [Mechanized Logical Relations for Termination-Insensitive Noninterference](https://iris-project.org/pdfs/2021-popl-tiniris-final.pdf) · POPL 2021 | [入口](https://github.com/logsem/iris-tini) | 使用 LR 证明 termination-insensitive noninterference |
| [Type-Directed Operational Semantics for Gradual Typing](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2021.12) · ECOOP 2021 | [入口](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.7.2.9) | 渐进类型语言的 type-directed 语义与性质 |
| [Consistent Subtyping for All](https://xnning.github.io/papers/consistent-subtyping-for-all-toplas.pdf) · TOPLAS 2020 | [入口](https://github.com/xnning/Consistent-Subtyping-for-All) | gradual polymorphism 与 consistent subtyping；ESOP 2018 不另计 |
| [Blame for Null](https://doi.org/10.4230/LIPIcs.ECOOP.2020.3) · ECOOP 2020 | [作者 artifact](https://doi.org/10.4230/DARTS.6.2.10) | 显式与隐式 nullability 的互操作、cast blame 和类型安全 |
| [Equivalences for Free: Univalent Parametricity for Effective Transport](https://doi.org/10.1145/3236787) · ICFP 2018 | [入口](https://github.com/CoqHott/univalent_parametricity) | 依赖类型中的 univalent parametricity 与 transport；区分形式化结果和实现插件 |

### 量子类型系统（1）

| 论文 | 公开代码 / artifact | 研究的问题 |
| --- | --- | --- |
| [Qafny: A Quantum-Program Verifier](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.24) · ECOOP 2024 | [作者源码](https://github.com/plum-umd/QNP/tree/aee7c4a13a96ec0c7411879f66f0032db1a31a69) | 定位量子数据的 locus 类型系统、类型可靠性及量子程序证明逻辑 |

## 其他线索：先不计入 Rocq 候选池

| 论文 | 已找到的材料 | 暂不计入的原因 |
| --- | --- | --- |
| [Divide and Check: Logical Relations, No Algorithms Attached](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2026.26) · FSCD 2026 | — | 用 LR 集中证明依赖类型论的 normalization、类型构造子 injectivity 等；未定位论文对应 Rocq 源码。 |
| [PLEX: Normalization for Refinement Types](https://doi.org/10.1145/3798248) · OOPSLA 2026 | [材料](https://zenodo.org/records/19126672) | 公开归档有实现及 Liquid Haskell、Agda 验证示例；未确认有 Rocq 证明。 |
| [AdapTT: Functoriality for Dependent Type Casts](https://doi.org/10.1145/3776664) · POPL 2026 | [材料](https://github.com/arthur-adjedj/AdapTT-agda) | 公开证明为 Agda。 |
| [Let Generalization, Polymorphic Recursion, and Variable Minimization in Boolean-Kinded Type Systems](https://doi.org/10.1145/3776644) · POPL 2026 | [材料](https://zenodo.org/records/17346848) | 公开归档是 OCaml 算法及类型检查器实现，未确认有 Rocq 证明。 |
| [Normalization by Evaluation for Non-cumulativity](https://doi.org/10.1145/3747508) · ICFP 2025 | [材料](https://zenodo.org/records/15611137) | 公开证明为 Agda。 |
| [Borrowing from Session Types](https://doi.org/10.1145/3763173) · OOPSLA 2025 | [材料](https://zenodo.org/records/16910888) | 公开归档包含 Agda 证明和 Idris2 示例，不是 Rocq。 |
| [Denotational Semantics of Gradual Typing using Synthetic Guarded Domain Theory](https://arxiv.org/abs/2411.12822) · POPL 2025 | — | 部分证明用 Guarded Cubical Agda。 |
| [Type Theory in Type Theory Using a Strictified Syntax](https://doi.org/10.1145/3747535) · ICFP 2025 | [材料](https://github.com/loic-p/cwf-strictification) | 公开证明为 Agda。 |
| [Observational Equality Meets CIC](https://pujet.fr/pdf/toplas25_cicobs.pdf) · TOPLAS 2025 | [证明](https://github.com/CoqHott/logrel-mltt/tree/impredicativity-cast-compute-refl) | 论文另有 Coq 内核实现，但 conversion 的元理论证明为 Agda。 |
| [All Your Base Are Belong to Us: Sort Polymorphism for Proof Assistants](https://doi.org/10.1145/3704912) · POPL 2025 | [材料](https://zenodo.org/records/13939644) | 有 Coq 原型；论文给出核心定理 proof sketches，尚未确认有对应 Rocq 证明。 |
| [Semantic Logical Relations for Timed Message-Passing Protocols](https://arxiv.org/abs/2411.07215) · POPL 2025 | — | 用 LR 证明类型化协议的时间保证；暂未定位 Rocq 证明。 |
| [Quest Complete: The Holy Grail of Gradual Security](https://arxiv.org/abs/2312.02359) · PLDI 2024 | [材料](https://github.com/cty12/pldi2024-ae) | 渐进信息流语言的元理论证明为 Agda。 |
| [Decidable Subtyping of Existential Types for Julia](https://pldi24.sigplan.org/details/pldi-2024-papers/45/Decidable-Subtyping-of-Existential-Types-for-Julia) · PLDI 2024 | — | 针对 Julia 的 existential subtyping；暂未定位 Rocq 证明。 |
| [Sound Borrow-Checking for Rust via Symbolic Semantics](https://arxiv.org/abs/2404.02680) · ICFP 2024 | — | 研究借用检查的 soundness；暂未定位 Rocq 证明。 |
| [Impredicative Observational Equality](https://doi.org/10.1145/3571739) · POPL 2023 | [材料](https://github.com/CoqHott/logrel-mltt/tree/impredicativity-SProp-POPL) | 公开证明为 Agda。 |
| [Is Sized Typing for Coq Practical?](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/is-sized-typing-for-coq-practical/9B55C4ABE4CB011CBD6405CA291FD920) · JFP 2023 | — | 在 Coq 内核实现 size inference；论文明确未解决该系统的强规范化和一致性证明。 |
| [Observational Equality: Now for Good](https://pujet.fr/pdf/OTT_now_for_good.pdf) · POPL 2022 | [材料](https://github.com/CoqHott/logrel-mltt/tree/setoid-universes-hierarchy) | normalization 和 canonicity 的公开证明为 Agda。 |
| [Gradualizing the Calculus of Inductive Constructions](https://doi.org/10.1145/3495528) · TOPLAS 2022 | [材料](https://github.com/pleiad/GradualizingCIC) | 论文配套源码为 Agda；与已收录的 *A Reasonably Gradual Type Theory* 不是同一篇。 |
| [COCHIS: Stable and Coherent Implicits](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/cochis-stable-and-coherent-implicits/F0127B641DC6AFBA1488A0C64A25A289) · JFP 2019 | [论文所列代码地址](https://bitbucket.org/KlaraMar/cochiscoq) | 附录明确用 Coq 证明部分结果，但尚未确认旧仓库目前可取。 |
| [Bidirectional Type Checking for Existential Types with Higher-Rank Polymorphism](https://link.springer.com/chapter/10.1007/978-3-032-22723-2_10) · ESOP 2026 | [材料](https://zenodo.org/records/18292979) | 归档说明给出算法实现，没有确认 Coq 证明。 |
| [Bounded Sort Polymorphism with Elimination Constraints](https://sozeau.gitlabpages.inria.fr/www/research/publications/drafts/sortpolyelim.pdf) · POPL 2026 | [材料](https://zenodo.org/records/17346329) | 归档说明给出原型实现；尚未确认有相应的 Rocq 元理论证明。 |
| [Extensible Data Types with Ad-Hoc Polymorphism](https://xnning.github.io/papers/popl26extensible.pdf) · POPL 2026 | [材料](https://zenodo.org/records/18102889) | 作者提供 Lean 证明。 |
| [Revisiting Soundness for Occurrence Typing, Semantically](https://arxiv.org/abs/2609.16299) · arXiv 2026 | — | 预印本；暂未确认 Rocq 代码。 |
| [Security Reasoning via Substructural Dependency Tracking](https://popl26.sigplan.org/details/POPL-2026-popl-research-papers/29/Security-Reasoning-via-Substructural-Dependency-Tracking) · POPL 2026 | — | 未找到 Rocq artifact。 |
| [Monadic Type-And-Effect Soundness](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2025.7) · ECOOP 2025 | — | 未找到 Rocq artifact。 |
| [Structural Information Flow: A Fresh Look at Types for Non-interference](https://doi.org/10.1145/3764116) · OOPSLA 2025 | — | 未找到 Rocq artifact。 |
| [Thrust: A Prophecy-Based Refinement Type System for Rust](https://doi.org/10.1145/3729333) · PLDI 2025 | [材料](https://github.com/coord-e/thrust) | 已找到工具实现，未确认语言级定理有 Rocq 证明。 |
| [Deciding Subtyping for Asynchronous Multiparty Sessions](https://arxiv.org/abs/2401.16395) · ESOP 2024 | — | 暂未确认有对应 Rocq 证明。 |
| [Parametric Subtyping for Structural Parametric Polymorphism](https://popl24.sigplan.org/details/POPL-2024-popl-research-papers/92/Parametric-Subtyping-for-Structural-Parametric-Polymorphism) · POPL 2024 | — | 暂未确认 Rocq 代码。 |
| [Soundly Handling Linearity](https://arxiv.org/abs/2307.09383) · POPL 2024 | [材料](https://zenodo.org/records/10120126) | 公开 artifact 介绍的是 Links 实现，未确认论文证明有 Coq 源码。 |
| [First-Class Names for Effect Handlers](https://xnning.github.io/papers/oopsla22namedh.pdf) · OOPSLA 2022 | [材料](https://zenodo.org/records/7062933) | 归档为 Koka 原型与示例；未找到 Coq 证明。 |
| [Giving Semantics to Program-Counter Labels via Secure Effects](https://arxiv.org/abs/2010.13191) · POPL 2021 | — | security typing 与 effect typing 的关系；暂未确认有对应 Rocq 代码。 |
| [A Mechanical Formalization of Higher-Ranked Polymorphic Type Inference](https://i.cs.hku.hk/~bruno/papers/icfp2019.pdf) · ICFP 2019 | [材料](https://github.com/JimmyZJX/TypingFormalization) | 公开证明为 Abella（`.thm`），不是 Coq。 |
| [Simple Noninterference from Parametricity](https://research.chalmers.se/publication/527412/file/527412_Fulltext.pdf) · ICFP 2019 | — | 从 parametricity 推出 noninterference；暂未确认有对应 Rocq 代码。 |
| [KafKa: Gradual Typing for Objects](https://2018.ecoop.org/details/ecoop-2018-papers/17/KafKa-Gradual-Typing-for-Objects) · ECOOP 2018 | [材料](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.4.3.10) | 有官方实现 artifact，尚未确认有对应 Rocq 证明。 |
| [Typed First-Class Traits](https://i.cs.hku.hk/~bruno/papers/traits.pdf) · ECOOP 2018 | [官方 artifact](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.4.3.9) | 官方 artifact 是带 traits 的 Haskell 原型；没有确认 Coq 证明。 |
| [A Relational Model of Types-and-Effects in Higher-Order Concurrent Separation Logic](https://popl17.sigplan.org/details/POPL-2017-papers/9/A-Relational-Model-of-Types-and-Effects-in-Higher-Order-Concurrent-Separation-Logic) · POPL 2017 | — | 待定位论文对应的公开 Rocq 源码。 |
| [Type Abstraction for Relaxed Noninterference](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2017.7) · ECOOP 2017 | [材料](https://drops.dagstuhl.de/entities/document/10.4230/DARTS.3.2.9) | 类型抽象用于信息流；公开 artifact 是工具实现，未找到 Rocq 证明。 |
| [Theorems for Free for Free: Parametricity, With and Without Types](https://doi.org/10.1145/3110283) · ICFP 2017 | — | 跟 System F free theorem 很接近，暂未确认有对应 Rocq 代码。 |

下一轮再筛：先看目标是否跟我们一样，要求 Agent 找到关键 LR、denotation 或其它语义不变量；然后定位确切的 `.v` 声明，查原始版本能否重放，最后排查同系列论文是否只是重复同一个核心证明。
