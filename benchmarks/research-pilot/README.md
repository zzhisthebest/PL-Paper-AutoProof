# Rocq 类型系统研究题集

共 100 道题，编号 **109–208**。每题来自原论文作者的 Coq/Rocq 源码，目标是论文的核心或重要形式化结果。原有 001–108 不计入本题集。

点击题名进入目录：`card.md` 说明任务，`input/` 提供必要定义和目标定理的陈述，不提供证明。同一结果的多个方向合在一道题里。[原始源码索引](../../docs/type-systems-benchmark-instances.md)

## 题目与出处

| 题目 | 论文 | 原文定理 / Rocq 声明 | 额外库 |
|---|---|---|---|
| [109 · Uniform intersection typability](109__uniform-intersection__typability) | [Mechanized Subject Expansion in Uniform Intersection Types for Perpetual Reductions](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2024.8) · FSCD 2024 | `nitlc_type_inference` | — |
| [110 · Ranked PTS strong normalization](110__ranked-pts__strong-normalization) | [A Sound Pure Type System with Ranks as Sorts and Type-in-Type](https://arxiv.org/abs/2610.25085) · arXiv 2026 | Thm. 5 | — |
| [111 · Effect subtyping coherence](111__effect-subtyping__coherence) | [Logical Relations for Coherence of Effect Subtyping](https://doi.org/10.23638/lmcs-14(1:11)2018) · LMCS 2018 | `coherence` | — |
| [112 · DOT interpreter safety](112__dot__interpreter-safety) | [Type Soundness Proofs with Definitional Interpreters](https://doi.org/10.1145/3009837.3009866) · POPL 2017 | `full_safety` | — |
| [113 · Intersection subtyping characterization](113__intersection-subtyping__logical-characterization) | [The Logic of Intersection Subtyping](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.62) · LICS 2026 | `is_bcd_equiv` | — |
| [114 · QuickSub subtyping correspondence](114__quicksub__subtyping-correspondence) | [QuickSub: Efficient Iso-Recursive Subtyping](https://ltzhou.com/static/POPL25.pdf) · POPL 2025 | Thms. 3.4, 3.6 | Metalib |
| [115 · Full iso-recursive cast correspondence](115__full-iso-recursive-types__cast-correspondence) | [Full Iso-Recursive Types](https://arxiv.org/abs/2407.00941) · OOPSLA 2024 | Thm. 3.1 | Metalib |
| [116 · Full iso-recursive behavior equivalence](116__full-iso-recursive-types__behavior-equivalence) | [Full Iso-Recursive Types](https://arxiv.org/abs/2407.00941) · OOPSLA 2024 | Thm. 3.9 | Metalib |
| [117 · Recursive kernel F-sub preservation](117__recursive-kernel-fsub__preservation) | [Recursive Subtyping for All](https://ltzhou.com/static/POPL23.pdf) · POPL 2023 | Thm. 3.6 | Metalib |
| [118 · Recursive kernel F-sub subtyping decidability](118__recursive-kernel-fsub__subtyping-decidability) | [Recursive Subtyping for All](https://ltzhou.com/static/POPL23.pdf) · POPL 2023 | Thm. 4.7 | Metalib |
| [119 · Dependent merges type safety](119__dependent-merges__type-safety) | [Dependent Merges and First-Class Environments](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.34) · ECOOP 2023 | `gen_type_safety` | Metalib |
| [120 · Compositional calculus type safety](120__compositional-calculus__type-safety) | [Direct Foundations for Compositional Programming](https://arxiv.org/abs/2205.06150) · ECOOP 2022 | `type_safety` | Metalib |
| [121 · Type-directed merges reduction soundness](121__type-directed-merges__reduction-soundness) | [A Type-Directed Operational Semantics for a Calculus with a Merge Operator](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2020.26) · ECOOP 2020 | Thm. 18 | Metalib |
| [122 · Gradual typing reduction soundness](122__gradual-typing__reduction-soundness) | [Type-Directed Operational Semantics for Gradual Typing](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2021.12) · ECOOP 2021 | Thm. 13 | Metalib |
| [123 · CBPV strong normalization](123__call-by-push-value__strong-normalization) | [Call-by-Push-Value in Coq: Operational, Equational, and Denotational Theory](https://doi.org/10.1145/3293880.3294097) · CPP 2019 | `strong_normalisation_cbpv` | — |
| [124 · Disjoint switches determinism](124__disjoint-switches__determinism) | [Union Types with Disjoint Switches](https://xnning.github.io/papers/ecoop22switches.pdf) · ECOOP 2022 | `determinism` | Metalib、TLC |
| [125 · Consistent subtyping conservative extension](125__consistent-subtyping__conservative-extension) | [Consistent Subtyping for All](https://xnning.github.io/papers/consistent-subtyping-for-all-toplas.pdf) · TOPLAS 2020 | `conservative_extension` | TLC |
| [126 · Iso-recursive subtyping Amber completeness](126__iso-recursive-subtyping__amber-completeness) | [Revisiting Iso-Recursive Subtyping](https://hub.hku.hk/handle/10722/322366) · TOPLAS 2022 | `amber_complete` | Metalib |
| [127 · Distributive disjoint polymorphism coherence](127__distributive-disjoint-polymorphism__coherence) | [Distributive Disjoint Polymorphism for Compositional Programming](https://xnning.github.io/papers/distributive-disjoint-polymorphism.pdf) · ESOP 2019 | Thm. 5 | Metalib |
| [128 · Effect handlers type soundness](128__effect-handlers__type-soundness) | [Handle with Care: Relational Interpretation of Algebraic Effects and Handlers](https://ii.uni.wroc.pl/~dabi/publications/POPL18/biernacki-al-popl18.pdf) · POPL 2018 | Thm. 9 | — |
| [129 · System F / λ2 bidirectional typability](129__system-f-lambda2__typing-correspondence) | [Relating System F and λ2: A Case Study in Coq, Abella and Beluga](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.21) · FSCD 2017 | Thms. 1–2 | Autosubst |
| [130 · Synchronous session types stuck freedom](130__synchronous-session-types__stuck-freedom) | [Formalising Subject Reduction and Progress for Multiparty Session Processes](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.19) · ITP 2025 | `stuck_free` | MathComp、Paco |
| [131 · Higher-order locks full reachability](131__higher-order-locks__full-reachability) | [Higher-Order Leak and Deadlock Free Locks](https://julesjacobs.com/papers/locks/) · POPL 2023 | Thm. 4.4 | stdpp |
| [132 · Multiparty GV deadlock freedom and full reachability](132__multiparty-gv__deadlock-freedom) | [Multiparty GV: Functional Multiparty Session Types with Certified Deadlock Freedom](https://iris-project.org/pdfs/2022-icfp-multiparty.pdf) · ICFP 2022 | `deadlock_freedom_and_full_reachability` | stdpp |
| [133 · pDOT type safety](133__pdot__type-safety) | [A Path to DOT: Formalizing Fully Path-Dependent Types](https://arxiv.org/abs/1904.07298) · OOPSLA 2019 | Thm. 5.1 | TLC |
| [134 · DOT syntactic type safety](134__dot__syntactic-type-safety) | [A Simple Soundness Proof for Dependent Object Types](https://arxiv.org/abs/1706.03814) · OOPSLA 2017 | `preservation`, `progress` | TLC |
| [135 · McTT NbE completeness](135__mctt__nbe-completeness) | [McTT: A Verified Kernel for a Proof Assistant](https://doi.org/10.1145/3747511) · ICFP 2025 | Thm. 4.8 | — |
| [136 · McTT NbE soundness](136__mctt__nbe-soundness) | [McTT: A Verified Kernel for a Proof Assistant](https://doi.org/10.1145/3747511) · ICFP 2025 | Thm. 4.15 | — |
| [137 · Multiparty session liveness](137__multiparty-sessions__liveness) | [Formally Verified Liveness with Multiparty Session Types in Rocq](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.4) · ITP 2026 | `liveness` | MathComp、Paco、MMaps |
| [138 · Disjoint polymorphism unique elaboration](138__disjoint-polymorphism__unique-elaboration) | [Disjoint Polymorphism](https://i.cs.hku.hk/~bruno/papers/ESOP2017.pdf) · ESOP 2017 | Thm. 4 | — |
| [139 · Local contextual type inference decidability](139__local-contextual-typing__decidability) | [Local Contextual Type Inference](https://i.cs.hku.hk/~bruno/papers/popl26.pdf) · POPL 2026 | Thm. 5.2 | — |
| [140 · Polymorphic reachability type safety](140__polymorphic-reachability__type-safety) | [Polymorphic Reachability Types: Tracking Freshness, Aliasing, and Separation in Higher-Order Generic Programs](https://www.cs.purdue.edu/homes/rompf/papers/wei-popl24.pdf) · POPL 2024 | `type_safety` | — |
| [141 · Row polymorphism elaboration type safety](141__row-polymorphism__elaboration-type-safety) | [Row and Bounded Polymorphism via Disjoint Polymorphism](https://xnning.github.io/papers/ecoop20row.pdf) · ECOOP 2020 | Thm. 14 | Metalib |
| [142 · Integrated subtyping decidability](142__integrated-subtyping__decidability) | [Empowering Union and Intersection Types with Integrated Subtyping](https://rosstate.org/publications/empower/empower-oopsla18.pdf) · OOPSLA 2018 | `IntegratedSoundness`, `IntegratedDecidability`, `IntegratedCompleteness`, `DecidabilityOfExtendedSubtyping` | — |
| [143 · Scoped arenas type safety](143__scoped-arenas__type-safety) | [When Lifetimes Liberate: A Type System for Arenas with Higher-Order Reachability Tracking](https://doi.org/10.1145/3798254) · OOPSLA 2026 | Thms. 5.3–5.4 | — |
| [144 · Cyclic reachability type safety](144__cyclic-reachability__type-safety) | [Complete the Cycle: Reachability Types with Expressive Cyclic References](https://sweetsinpackets.github.io/file/cycle-paper.pdf) · OOPSLA 2025 | `type_safety` | — |
| [145 · Bounded polymorphism elaboration type safety](145__bounded-polymorphism__elaboration-type-safety) | [Row and Bounded Polymorphism via Disjoint Polymorphism](https://xnning.github.io/papers/ecoop20row.pdf) · ECOOP 2020 | Thm. 19 | Metalib |
| [146 · Martin-Löf type theory NbE completeness](146__martin-lof-type-theory__nbe-completeness) | [A Coq Formalization of Normalization by Evaluation for Martin-Löf Type Theory](https://ii.uni.wroc.pl/~dabi/publications/CPP18/wieczorek-biernacki-cpp18.pdf) · CPP 2018 | `NBE_Completeness` | — |
| [147 · Martin-Löf type theory NbE soundness](147__martin-lof-type-theory__nbe-soundness) | [A Coq Formalization of Normalization by Evaluation for Martin-Löf Type Theory](https://ii.uni.wroc.pl/~dabi/publications/CPP18/wieczorek-biernacki-cpp18.pdf) · CPP 2018 | `Nbe_Soundness` | — |
| [148 · CBPV effects and coeffects soundness](148__cbpv-effects-coeffects__soundness) | [Effects and Coeffects in Call-by-Push-Value](https://arxiv.org/abs/2311.11795) · OOPSLA 2024 | `soundness` | — |
| [149 · Dependent Dependency Calculus noninterference](149__dependent-dependency-calculus__noninterference) | [A Dependent Dependency Calculus](https://par.nsf.gov/servlets/purl/10318626) · ESOP 2022 | Thm. 8 and Lemma 9 | Metalib |
| [150 · CBN/CBV translations to CBPV with effects and coeffects](150__cbpv-effects-coeffects__translation-type-safety) | [Effects and Coeffects in Call-by-Push-Value](https://arxiv.org/abs/2311.11795) · OOPSLA 2024 | Thm. 5.8 | — |
| [151 · DCOIω logical consistency](151__dcoi-omega__logical-consistency) | [Consistency of a Dependent Calculus of Indistinguishability](https://www.cis.upenn.edu/~sweirich/papers/popl25.pdf) · POPL 2025 | Cor. 5.24 | stdpp |
| [152 · Self-dual session type encodings](152__self-dual-session-types__typing-admissibility) | [A Self-Dual Distillation of Session Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.23) · ECOOP 2022 | `ForkB_typed`, `SendB_typed`, `RecvB_typed`, `CloseB_typed` | stdpp |
| [153 · Refinement Featherweight Java type soundness](153__refinement-featherweight-java__type-soundness) | [Formalizing, Mechanizing, and Verifying Class-Based Refinement Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.39) · ECOOP 2024 | Thm. 1 / Cor. 15 | — |
| [154 · Refinement Featherweight Java logical soundness](154__refinement-featherweight-java__logical-soundness) | [Formalizing, Mechanizing, and Verifying Class-Based Refinement Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.39) · ECOOP 2024 | Thm. 2 / Cor. 16 | — |
| [155 · System C type safety](155__system-c__type-safety) | [Effects, Capabilities, and Boxes](https://plg.uwaterloo.ca/~e45lee/publication/boxes/boxes.pdf) · OOPSLA 2022 | `preservation_step`, `progress_step` | — |
| [156 · Box capture calculus type safety](156__box-capture-calculus__type-safety) | [A Mechanized Theory of the Box Calculus](https://arxiv.org/abs/2309.05362) · IWACO 2023 | `preservation`, `progress` | — |
| [157 · Application contexts: Hindley–Milner conservativity](157__application-contexts__hindley-milner-conservativity) | [Let Arguments Go First](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_10) · ESOP 2018 | Lemma 3 (§3.2) | TLC |
| [158 · Application contexts: System F elaboration](158__application-contexts__system-f-elaboration) | [Let Arguments Go First](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_10) · ESOP 2018 | Lemma 9 (§3.4) | TLC |
| [159 · Explicit application contexts: type safety](159__explicit-application-contexts__type-safety) | [Let Arguments Go First](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_10) · ESOP 2018 | `typing_preservation`, `typing_progress` | TLC |
| [160 · Application contexts: elaboration coherence](160__application-contexts__elaboration-coherence) | [Let Arguments Go First](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_10) · ESOP 2018 | Lemma 10 (§3.4) | TLC |
| [161 · Definitional proof irrelevance: computational canonicity](161__proof-irrelevance__computational-canonicity) | [Definitional Proof Irrelevance Made Accessible](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.41) · LICS 2026 | `computational_canonicity` | — |
| [162 · GraD dependent type safety](162__grad__dependent-type-safety) | [A Graded Dependent Type System with a Usage-Aware Semantics](https://doi.org/10.1145/3434331) · POPL 2021 | Thms. 7.4–7.5 | Metalib |
| [163 · Duotyping subtyping correspondence](163__duotyping__subtyping-correspondence) | [The Duality of Subtyping](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2020.29) · ECOOP 2020 | `sound`, `complete` | — |
| [164 · NeColus contextual elaboration coherence](164__necolus__contextual-elaboration-coherence) | [The Essence of Nested Composition](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2018.22) · ECOOP 2018 | `coherence_thm` | Metalib |
| [165 · NeColus subtyping algorithm correctness](165__necolus__subtyping-correspondence) | [The Essence of Nested Composition](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2018.22) · ECOOP 2018 | Thms. 25, 31 | Metalib |
| [166 · Strong kernel D<: stare-at correspondence](166__strong-kernel-dsub__stare-at-correspondence) | [Undecidability of D<: and Its Decidable Fragments](https://arxiv.org/abs/1908.05294) · POPL 2020 | Thms. 44, 46 | Metalib |
| [167 · Unified typing and subtyping: type safety](167__unified-typing-subtyping__type-safety) | [Unifying Typing and Subtyping](https://doi.org/10.1145/3133871) · OOPSLA 2017 | Lemmas 4.13, 4.17 | TLC |
| [168 · Unified typing and subtyping: bidirectional correspondence](168__unified-typing-subtyping__bidirectional-correspondence) | [Unifying Typing and Subtyping](https://doi.org/10.1145/3133871) · OOPSLA 2017 | Thms. 5.1–5.2 | TLC |
| [169 · Gradual polymorphism with references: gradual guarantees](169__gradual-polymorphism-references__gradual-guarantees) | [Pragmatic Gradual Polymorphism with References](https://link.springer.com/chapter/10.1007/978-3-031-30044-8_6) · ESOP 2023 | Thms. 8, 10 | Metalib |
| [170 · Gradual polymorphism with references: type safety](170__gradual-polymorphism-references__type-safety) | [Pragmatic Gradual Polymorphism with References](https://link.springer.com/chapter/10.1007/978-3-031-30044-8_6) · ESOP 2023 | Thms. 5–6 | Metalib |
| [171 · Deep handlers to shift₀: typed translation](171__deep-handlers-shift0__typing-preservation) | [Typed Equivalence of Effect Handlers and Delimited Control](https://doi.org/10.4230/LIPIcs.FSCD.2019.30) · FSCD 2019 | Thms. 5–6 | — |
| [172 · Type-outference: validity decidability](172__type-outference__validity-decidability) | [Type-Outference with Label-Listeners](https://doi.org/10.1145/3763797) · OOPSLA 2025 | Thm. 9.7 | — |
| [173 · Type-outference: type safety](173__type-outference__type-safety) | [Type-Outference with Label-Listeners](https://doi.org/10.1145/3763797) · OOPSLA 2025 | Thm. 7.3 | — |
| [174 · Higher-kinded GADT type safety](174__higher-kinded-gadt__type-safety) | [The Essence of Generalized Algebraic Data Types](https://doi.org/10.1145/3632866) · POPL 2024 | Thm. 4.6 | — |
| [175 · roDOT with pure methods: type safety](175__rodot-pure-methods__type-safety) | [Pure Methods for roDOT](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.13) · ECOOP 2024 | Thm. 1 | TLC |
| [176 · roDOT with pure methods: side-effect freedom](176__rodot-pure-methods__side-effect-freedom) | [Pure Methods for roDOT](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.13) · ECOOP 2024 | Thm. 16 | TLC |
| [177 · Typing Strictness: CBN-to-CBPV translation](177__typing-strictness__cbn-cbpv-translation) | [Typing Strictness](https://doi.org/10.1145/3776657) · POPL 2026 | Thm. 4.5 | — |
| [178 · Oblivious algebraic data types: trace obliviousness](178__oblivious-adts__trace-obliviousness) | [Oblivious Algebraic Data Types](https://doi.org/10.1145/3498713) · POPL 2022 | Thm. 4.4 | stdpp |
| [179 · Oblivious algebraic data types: type safety](179__oblivious-adts__type-safety) | [Oblivious Algebraic Data Types](https://doi.org/10.1145/3498713) · POPL 2022 | `soundness` | stdpp |
| [180 · Type-directed merges: type safety](180__type-directed-merges__type-safety) | [A Type-Directed Operational Semantics for a Calculus with a Merge Operator](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2020.26) · ECOOP 2020 | Thms. 16–17 | Metalib |
| [181 · Internalizing indistinguishability: noninterference](181__dependent-indistinguishability__noninterference) | [Internalizing Indistinguishability with Dependent Types](https://doi.org/10.1145/3632886) · POPL 2024 | Thm. 4.31 | Metalib、MathComp |
| [182 · Internalizing indistinguishability: type safety](182__dependent-indistinguishability__type-safety) | [Internalizing Indistinguishability with Dependent Types](https://doi.org/10.1145/3632886) · POPL 2024 | Thms. 4.24, 4.29 | Metalib、MathComp |
| [183 · Dependent polymorphic subtyping: type safety under erasure](183__dependent-polymorphic-subtyping__erased-type-safety) | [A Dependently Typed Calculus with Polymorphic Subtyping](https://doi.org/10.1016/j.scico.2021.102655) · SCP 2021 | `generalized_erased_progress`, `preservation` | Metalib |
| [184 · Pure iso-type systems: type-checking decidability](184__pure-iso-type-systems__type-checking-decidability) | [Pure Iso-Type Systems](https://doi.org/10.1017/S0956796819000108) · JFP 2019 | Thm. 6.3 | TLC |
| [185 · Pure iso-type systems: type safety after erasure](185__pure-iso-type-systems__erasure-type-safety) | [Pure Iso-Type Systems](https://doi.org/10.1017/S0956796819000108) · JFP 2019 | `subject_reduction_result`, `progress_result` | TLC |
| [186 · Dependent polymorphic subtyping: transitivity](186__dependent-polymorphic-subtyping__transitivity) | [A Dependently Typed Calculus with Polymorphic Subtyping](https://doi.org/10.1016/j.scico.2021.102655) · SCP 2021 | `transitivity` | Metalib |
| [187 · Disjoint switches: disjointness correspondence](187__disjoint-switches__disjointness-correspondence) | [Union Types with Disjoint Switches](https://xnning.github.io/papers/ecoop22switches.pdf) · ECOOP 2022 | Thm. 5 | TLC |
| [188 · Dependent Haskell: annotated type safety](188__dependent-haskell__annotated-type-safety) | [A Specification for Dependent Types in Haskell](https://doi.org/10.1145/3110275) · ICFP 2017 | Lemmas 5.8, 5.12 | Metalib |
| [189 · Dependent Haskell: erasure and annotation](189__dependent-haskell__erasure-annotation-correspondence) | [A Specification for Dependent Types in Haskell](https://doi.org/10.1145/3110275) · ICFP 2017 | Lemmas 5.4–5.5 | Metalib |
| [190 · System DR: role-indexed type safety](190__system-dr__role-indexed-type-safety) | [A Role for Dependent Types in Haskell](https://doi.org/10.1145/3341705) · ICFP 2019 | Lemmas 5.11, 5.14–5.15 | Metalib |
| [191 · Disjoint switches: type safety](191__disjoint-switches__type-safety) | [Union Types with Disjoint Switches](https://xnning.github.io/papers/ecoop22switches.pdf) · ECOOP 2022 | Thms. 21–22 | Metalib、TLC |
| [192 · Higher-rank inference with intersections and unions: correctness](192__higher-rank-unions-intersections__inference-correctness) | [Bidirectional Higher-Rank Polymorphism with Intersection and Union Types](https://doi.org/10.1145/3704907) · POPL 2025 | Thm. 4.1 | Metalib |
| [193 · Higher-rank inference with intersections and unions: decidability](193__higher-rank-unions-intersections__worklist-decidability) | [Bidirectional Higher-Rank Polymorphism with Intersection and Union Types](https://doi.org/10.1145/3704907) · POPL 2025 | Thm. 4.2 | Metalib |
| [194 · Second-class values: instrumented type soundness](194__second-class-values__instrumented-type-soundness) | [What If We Don't Pop the Stack? The Return of 2nd-Class Values](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.15) · ECOOP 2022 | Thm. 3 | — |
| [195 · Second-class values: stack evaluation equivalence](195__second-class-values__stack-evaluation-equivalence) | [What If We Don't Pop the Stack? The Return of 2nd-Class Values](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.15) · ECOOP 2022 | Thm. 5 | — |
| [196 · iDOT: type and initialization safety](196__idot__type-and-initialization-safety) | [ιDOT: A DOT Calculus with Object Initialization](https://doi.org/10.1145/3428276) · OOPSLA 2020 | Thm. 5.1 | TLC |
| [197 · Dependent Haskell: closed-term type-checking decidability](197__dependent-haskell__type-checking-decidability) | [A Specification for Dependent Types in Haskell](https://doi.org/10.1145/3110275) · ICFP 2017 | Lemma 5.2 (closed-term version, `FC_typechecker`) | Metalib |
| [198 · Blame for Null: explicit nullability and blame](198__blame-for-null__explicit-nullability-blame) | [Blame for Null](https://doi.org/10.4230/LIPIcs.ECOOP.2020.3) · ECOOP 2020 | Thm. 22 | Metalib |
| [199 · Blame for Null: base-calculus type safety](199__blame-for-null__base-type-safety) | [Blame for Null](https://doi.org/10.4230/LIPIcs.ECOOP.2020.3) · ECOOP 2020 | Lemmas 5, 8 | Metalib |
| [200 · Blame for Null: type preservation of desugaring](200__blame-for-null__desugaring-type-preservation) | [Blame for Null](https://doi.org/10.4230/LIPIcs.ECOOP.2020.3) · ECOOP 2020 | Thm. 20 | Metalib |
| [201 · Polymorphic reachability: preservation of separation](201__polymorphic-reachability__preservation-of-separation) | [Polymorphic Reachability Types: Tracking Freshness, Aliasing, and Separation in Higher-Order Generic Programs](https://www.cs.purdue.edu/homes/rompf/papers/wei-popl24.pdf) · POPL 2024 | `preservation_of_separation` (polymorphic calculus, §5) | — |
| [202 · McTT: bidirectional type-checking correctness](202__mctt__bidirectional-type-checking-correctness) | [McTT: A Verified Kernel for a Proof Assistant](https://doi.org/10.1145/3747511) · ICFP 2025 | Thms. 5.5–5.6 (checking clauses) | — |
| [203 · PICO: abstract-state preservation](203__pico__abstract-state-preservation) | [Transitive, Abstract, and Class Polymorphic Immutability](https://doi.org/10.1145/3839491) · OOPSLA 2026 | Thm. 3 (abstract state) | — |
| [204 · PICO: type preservation and mutation safety](204__pico__type-and-mutation-safety) | [Transitive, Abstract, and Class Polymorphic Immutability](https://doi.org/10.1145/3839491) · OOPSLA 2026 | Thm. 1 | — |
| [205 · PICO: readonly and transitive state preservation](205__pico__readonly-state-preservation) | [Transitive, Abstract, and Class Polymorphic Immutability](https://doi.org/10.1145/3839491) · OOPSLA 2026 | Thm. 4 (RS and TS clauses) | — |
| [206 · Full iso-recursive types with subtyping: type safety](206__full-iso-recursive-subtyping__type-safety) | [Full Iso-Recursive Types](https://arxiv.org/abs/2407.00941) · OOPSLA 2024 | Thm. 5.4 | Metalib |
| [207 · Typed tree calculus: type preservation](207__typed-tree-calculus__type-preservation) | [Typed Program Analysis Without Encodings](https://doi.org/10.1145/3704253.3706138) · PEPM 2025 | Thm. 20 | — |
| [208 · System F<: with mutable references: interpreter safety](208__fsub-mutable-references__interpreter-safety) | [Type Soundness Proofs with Definitional Interpreters](https://doi.org/10.1145/3009837.3009866) · POPL 2017 | Thm. 4 (§4.1) | — |

## 题面检查

使用 Rocq 9.1.0。在仓库根目录运行：

```bash
python scripts/check_research_pilot.py            # 检查全部题面
python scripts/check_research_pilot.py 109 110 111 # 只检查指定题面
```

脚本在临时副本中结束待证明的目标，只检查定义和定理陈述能否加载。完成证明后，可用各题的 `_CoqProject` 编译。

- Metalib、TLC：使用 [Metalib `144ddcd`](https://github.com/plclub/metalib/tree/144ddcd0fff6717229140314cf559d85fad6eae0) 和 [TLC `b35ec77`](https://github.com/charguer/tlc/tree/b35ec775e8559180bdbbfd1d9d5d82afad23678d)，将包含库逻辑目录的路径加入 `ROCQPATH`。
- 129–130、137、181–182：依赖版本见 [构建脚本](../../scripts/build_research_case_libraries.sh)。运行 `bash scripts/build_research_case_libraries.sh /tmp/rocq-research-libraries --mmaps`，再将 `/tmp/rocq-research-libraries/lib` 加入 `ROCQPATH`。
- 131–132、151–152、178–179：使用 `rocq-stdpp.1.13.0`。

对外发布前仍需核对部分原始 artifact 的再分发许可。
