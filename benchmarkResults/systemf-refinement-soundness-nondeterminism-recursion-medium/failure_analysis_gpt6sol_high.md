# systemf-refinement-soundness-nondeterminism-recursion-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

这次运行停在**从局部辅助引理组织出整体逻辑关系证明**：agent 证明了指称、蕴涵、选择等若干引理，却没有建立“精化类型推导在环境实例化后得到 `evals_denotes`”所需的归纳证明，也没有完成子类型的语义保持证明。它因此只能把 `never_stuck` 归约为一个尚未证明的前提。

应用、子类型和递归规则都需要处理更复杂的语义义务；但 trace **没有显示 agent 在其中某个具体分支上反复尝试并失败**。所以不能仅凭最终回复断定递归度量或某条替换引理就是唯一根因。更有把握的判断是：它未能从已验证的基础引理推进到覆盖类型规则的主证明。

## 关键证据

- [result](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-recursion-medium/results_gpt6sol_high.json) 记录状态为 `failed`，耗时 519 秒。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-recursion-medium/proofs_gpt6sol_high/systemf-refinement-soundness-nondeterminism-recursion-medium.v:1543) 中，`safety_from_closed_fundamental` **把闭项的 `evals_denotes` 结论作为前提**；其后的 `never_stuck` 证明体为空。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-recursion-medium/traces_gpt6sol_high/systemf-refinement-soundness-nondeterminism-recursion-medium.jsonl:129) 的最终编译错误是保存 `never_stuck` 时仍有未完成目标。此前新增引理的编译错误有过修正；trace 未记录针对主定理某个归纳分支的连续失败。
- 当前 [原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-nondeterminism-recursion-medium/input/Task.v.orig) 与最终文件的原有部分一致，差异是任务模块中新增的证明内容；当前 [卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-nondeterminism-recursion-medium/card.md) 与该目标相符。未发现会改变本次判断的题面差异。
