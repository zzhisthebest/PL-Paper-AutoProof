# systemf-refinement-soundness-if-recursion-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

证明停在从 `has_rtype` 推出 `evals_denotes` 的 **fundamental theorem**：最终文件已证明“满足 `evals_denotes` 就不会卡住”，却没有证明目标程序满足这一前提。

更具体的能力瓶颈是**把逻辑关系推广到完整的类型规则归纳**。trace 中两次尝试该归纳后，仍留下函数抽象、应用、子类型和递归等构造的义务；函数抽象始终是首个未解决目标，需要处理环境扩展与局部无名变量的开放、替换。证据不足以断定递归度量是唯一或最主要的难点，因为运行尚未完成前面的构造案例。

## 关键证据

- [结果记录](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-recursion-medium/results_gpt6sol_high.json)标记为 `failed`。trace 中 fundamental theorem 的编译输出先有 15 个目标，处理少数简单案例后仍有 12 个；再次尝试仍为 12 个，[函数抽象目标排在首位](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-recursion-medium/traces_gpt6sol_high/systemf-refinement-soundness-if-recursion-medium.jsonl:109)。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-recursion-medium/proofs_gpt6sol_high/systemf-refinement-soundness-if-recursion-medium.v:1433)只有变量、整数、布尔值等单项辅助引理，没有完整的 fundamental theorem；`never_stuck` 调用语义引理后仍缺 `evals_denotes R t`。最后一次编译因此报未完成证明。
- trace 起始时读取的 `Task.v` 与[当前原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-recursion-medium/input/Task.v.orig)逐字一致；当时读取的卡片也与[当前卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-recursion-medium/card.md)一致。本次没有发现题面版本差异。
