# systemf-refinement-soundness-nondeterminism-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

运行停在 `never_stuck`，但编译报出的“未解子目标”只是结果。主要瓶颈是：agent 没有建立可用于开放上下文归纳的完整语义基础。它在多态类型应用处反复无法把良基递归定义的 `interpret_value` 展开成可用结论；随后提出的上下文解释又不足以直接处理最先出现的变量分支。除法和非确定选择已有通过检查的辅助证明，未显示为主要阻碍。

## 关键证据

- [结果文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-hard/results_gpt6sol_high.json)记为 `failed`。最终文件只[定义了 `fundamental_property`](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-hard/proofs_gpt6sol_high/systemf-refinement-soundness-nondeterminism-hard.v:1363)，却没有证明它；[目标定理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-hard/proofs_gpt6sol_high/systemf-refinement-soundness-nondeterminism-hard.v:1388)将它留作未解前提，trace 中编译在 `Qed` 处失败。
- [运行 trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-hard/traces_gpt6sol_high/systemf-refinement-soundness-nondeterminism-hard.jsonl)显示，多次尝试证明多态值的应用性质时，`Program Fixpoint` 展开后产生的递归调用与目标中的 `interpret_value` 无法直接匹配；相关引理最终被删去。之后 agent 仅展开基本引理的 11 个归纳目标，并查看了第一个变量目标，未完成任何完整的基本引理归纳。
- [上下文解释](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-hard/proofs_gpt6sol_high/systemf-refinement-soundness-nondeterminism-hard.v:1038)约束的是 `rho x`，而[项实例化](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-hard/proofs_gpt6sol_high/systemf-refinement-soundness-nondeterminism-hard.v:1010)会顺序替换上下文变量；定义没有保证 `rho x` 不会被其他替换再次改写。这具体解释了为何变量分支不能直接由上下文假设完成。更后面的依赖精化与子类型分支是否还有独立障碍，现有 trace 不足以确认。
- 当前 [card](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-nondeterminism-hard/card.md)与 trace 中读取的卡片一致；当前 [Task.v.orig](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-nondeterminism-hard/input/Task.v.orig)与最终证明文件的原始前缀一致，未见题面变更。
