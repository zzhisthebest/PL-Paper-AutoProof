# systemf-refinement-soundness-if-nondeterminism-recursion-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

运行停在 `never_stuck` 的空证明；直接原因是没有建立把精化类型推导转成 `evals_denotes` 的基本引理。trace 中**最明确、反复出现的能力瓶颈**是组合式语义证明：处理条件式时，agent 未能完成“条件求值必终止、两分支均满足关系，因此整个条件式必终止且所有可达结果满足关系”的辅助引理，最终将其删除。函数、多态、子类型和递归也留有证明义务，但 trace 没有逐一攻克它们的记录，不能确认哪一个才是更深的根因。

## 关键证据

- [结果文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-recursion-medium/results_gpt6sol_high.json) 记录 `failed`、耗时 939 秒。[最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-recursion-medium/proofs_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-recursion-medium.v:1487) 中 `never_stuck` 仍是空证明；trace 的最后编译报错是“remaining open goals”。这是**停在哪**，不是根因。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-recursion-medium/traces_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-recursion-medium.jsonl) 显示，基本引理展开后有 16 个目标；处理变量、常量和选择等简单情况后仍有 11 个。此后 agent 多次修改 `evals_denotes_if`，检查 `must_terminate` 及各步可达结果的目标，出现长时间无输出的编译尝试，最后删除了该未完成引理和基本引理草稿。局部引理虽已加入文件，却没有接成完整证明。
- 当前 [card](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-nondeterminism-recursion-medium/card.md) 的内容与 trace 中读到的卡片一致；当前 [Task.v.orig](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-nondeterminism-recursion-medium/input/Task.v.orig) 与最终证明文件的原有部分一致，后者仅在任务模块追加了内容。未发现当前题面与当时题面不一致的证据。
