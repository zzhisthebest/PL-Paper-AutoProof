# GPT-6 Sol High：Hard / Medium 运行结果

统计日期：2026-09-25。结果 tag 为 `gpt6sol_high`；模型为 `gpt-6-sol`，reasoning effort 为 `high`，每题限时 3600 秒。本轮运行 72 道 Hard / Medium 题，不包括 Easy。Hard 不提供 LR，但提示先设计并检验 LR；Medium 提供 LR。此前四题的“重构 LR”实验使用独立 tag，不计入本页。

这里的 `proved` 是测试脚本记录的“Rocq 编译通过”；`failed` 是运行结束但未通过编译；`timeout` 是达到限时。逐题原始结果、trace、最终文件和失败报告均在 [`benchmarkResults/`](../benchmarkResults/) 中。

| 题目类别 | 编译通过 | Failed | Timeout |
|---|---:|---:|---:|
| STLC normalization | 16 | 0 | 0 |
| System F normalization | 15 | 1 | 0 |
| System F parametricity | 14 | 2 | 0 |
| System F refinement type safety | 0 | 16 | 0 |
| Security noninterference | 4 | 0 | 4 |
| 合计 | 49 | 19 | 4 |

## 从 23 份未完成报告看到什么

- **主要缺口是整体证明，而非最后一条 tactic。** 大多数运行完成了若干求值、逻辑关系或安全性辅助引理，却没有建立开放上下文中的基本定理：从 typing（refinement 题还包括 subtyping）推到相应的语义关系。[refinement none-hard](../benchmarkResults/systemf-refinement-soundness-none-hard/failure_analysis_gpt6sol_high.md) 是典型例子。
- **局部引理难以接回主线。** 有些 agent 直到运行后期才展开基本定理；[if + recursion Medium](../benchmarkResults/systemf-refinement-soundness-if-recursion-medium/failure_analysis_gpt6sol_high.md) 实际展开后，函数抽象中的环境扩展、打开与替换成为首个未解目标。在 8 对 refinement Hard / Medium 题中，提供 LR 的 Medium 也全部未完成；仅给出 LR 没有打通这批题的主要缺口。
- **不能把尚未到达的分支判为根因。** 多数 trace 没有逐一尝试递归、非确定性或全部子类型分支；现有证据也不能确认候选 LR 一定正确或错误。4 个 noninterference Medium 达到 3600 秒，其中 [None](../benchmarkResults/security-noninterference-none-medium/failure_analysis_gpt6sol_high.md) 在运行中曾编译通过基本定理，但最终程序上下文定理仍未证明；其余 3 题尚未完成基本定理。

这些是对**本轮 agent 行为**的观察，不是对题目固有难度或某一种 LR 设计的定论。逐题报告也区分了直接观察到的停点与对能力缺口的推测。

## 值得先试的方法

1. **先展开主证明，再补辅助引理。** 要求 agent 尽早提出开放上下文版本的基本定理，按 typing / subtyping 规则展开归纳，记录真实的未解证明义务；之后每个辅助引理都对应一个具体义务。Hard 题构造 LR 后，也应立即用这些义务检查它是否够强，不够时先修改 LR。
2. **针对反复出现的接口提供工具支持。** 如果第一项实验确认瓶颈集中在绑定规则，可尝试让 agent 检索或生成 locally nameless 的打开、替换、环境扩展引理，以及 refinement typing 与 subtyping 的联合归纳框架。先作为 agent 方法试验，不直接改 benchmark 输入。
3. **单独处理最终衔接。** 对基本定理已经建立的 noninterference 题，测试 agent 能否构造“相关输入放入有类型程序上下文后仍相关”的桥接引理；它和基本定理缺失不是同一个问题。

建议先选 refinement None 的 Hard / Medium、System F parametricity If + Recursion Medium、Security Noninterference None Medium 做同模型、同预算的 A/B 小实验。除最终成功率，还记录开始基本定理归纳的时间、实际关闭的 typing / subtyping 分支数，以及是否识别并修正了 LR 或环境解释中的缺口。

## 逐题失败报告

Security noninterference（4 个 timeout）：[None Medium](../benchmarkResults/security-noninterference-none-medium/failure_analysis_gpt6sol_high.md) · [If Medium](../benchmarkResults/security-noninterference-if-medium/failure_analysis_gpt6sol_high.md) · [Recursion Medium](../benchmarkResults/security-noninterference-recursion-medium/failure_analysis_gpt6sol_high.md) · [If + Recursion Medium](../benchmarkResults/security-noninterference-if-recursion-medium/failure_analysis_gpt6sol_high.md)。

System F normalization / parametricity（3 个 failed）：[Normalization If + Recursion Medium](../benchmarkResults/systemf-normalization-if-recursion-medium/failure_analysis_gpt6sol_high.md) · [Parametricity If + Recursion Medium](../benchmarkResults/systemf-parametricity-if-recursion-medium/failure_analysis_gpt6sol_high.md) · [Parametricity Non-determinism + Recursion Hard](../benchmarkResults/systemf-parametricity-nondeterminism-recursion-hard/failure_analysis_gpt6sol_high.md)。

System F refinement type safety（16 个 failed）：

| Feature | Hard 报告 | Medium 报告 |
|---|---|---|
| None | [Hard](../benchmarkResults/systemf-refinement-soundness-none-hard/failure_analysis_gpt6sol_high.md) | [Medium](../benchmarkResults/systemf-refinement-soundness-none-medium/failure_analysis_gpt6sol_high.md) |
| If | [Hard](../benchmarkResults/systemf-refinement-soundness-if-hard/failure_analysis_gpt6sol_high.md) | [Medium](../benchmarkResults/systemf-refinement-soundness-if-medium/failure_analysis_gpt6sol_high.md) |
| Non-determinism | [Hard](../benchmarkResults/systemf-refinement-soundness-nondeterminism-hard/failure_analysis_gpt6sol_high.md) | [Medium](../benchmarkResults/systemf-refinement-soundness-nondeterminism-medium/failure_analysis_gpt6sol_high.md) |
| Recursion | [Hard](../benchmarkResults/systemf-refinement-soundness-recursion-hard/failure_analysis_gpt6sol_high.md) | [Medium](../benchmarkResults/systemf-refinement-soundness-recursion-medium/failure_analysis_gpt6sol_high.md) |
| If + Non-determinism | [Hard](../benchmarkResults/systemf-refinement-soundness-if-nondeterminism-hard/failure_analysis_gpt6sol_high.md) | [Medium](../benchmarkResults/systemf-refinement-soundness-if-nondeterminism-medium/failure_analysis_gpt6sol_high.md) |
| If + Recursion | [Hard](../benchmarkResults/systemf-refinement-soundness-if-recursion-hard/failure_analysis_gpt6sol_high.md) | [Medium](../benchmarkResults/systemf-refinement-soundness-if-recursion-medium/failure_analysis_gpt6sol_high.md) |
| Non-determinism + Recursion | [Hard](../benchmarkResults/systemf-refinement-soundness-nondeterminism-recursion-hard/failure_analysis_gpt6sol_high.md) | [Medium](../benchmarkResults/systemf-refinement-soundness-nondeterminism-recursion-medium/failure_analysis_gpt6sol_high.md) |
| If + Non-determinism + Recursion | [Hard](../benchmarkResults/systemf-refinement-soundness-if-nondeterminism-recursion-hard/failure_analysis_gpt6sol_high.md) | [Medium](../benchmarkResults/systemf-refinement-soundness-if-nondeterminism-recursion-medium/failure_analysis_gpt6sol_high.md) |
