# security-noninterference-none-medium

Run tag: `gpt6sol_high`  
Recorded status: `timeout`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

**证明停在最后的 `noninterference` 定理，而不是停在 fundamental theorem。** Agent 已补出 `fundamental_low`，但在 3600 秒超时前，没有把它用于任意闭合项填入程序上下文的最终证明；目标定理仍是 `Admitted`。

更主要的能力瓶颈是**组织并推进这条较长的逻辑关系证明链**。运行时间大量花在补建绑定变量替换、擦除后类型保持、求值分解，以及运行时安全标签变化下的关系保持等引理上。trace 显示投影和 `case` 等分支反复出现未闭合义务。至于最后的上下文代入步骤，trace 没有足够证据说明 agent 在那一步遇到了具体错误，因为它尚未开始证明该定理。

## 关键证据

- [结果记录](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-none-medium/results_gpt6sol_high.json)为 `timeout`，耗时 3600 秒；token 用量字段为空。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-none-medium/proofs_gpt6sol_high/security-noninterference-none-medium.v:2598)中 `fundamental_low` 以 `Qed` 结束，随后[目标定理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-none-medium/proofs_gpt6sol_high/security-noninterference-none-medium.v:2908)仍以 `Admitted` 结束。trace 后期也记录了 `coqc Task.v` 成功，因此不能把 fundamental theorem 未完成当作根因。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-none-medium/traces_gpt6sol_high/security-noninterference-none-medium.jsonl:525)进入 fundamental theorem 后，连续记录投影、`case` 等分支的未闭合义务；最终文件为此加入了[运行时标签变化引理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-none-medium/proofs_gpt6sol_high/security-noninterference-none-medium.v:2397)和[`case` 求值关系引理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-none-medium/proofs_gpt6sol_high/security-noninterference-none-medium.v:2549)。这比最后一次 tactic 报错更能说明耗时所在。
- 当前 [Task.v.orig](/data0/zzh/PL-Paper-AutoProof/benchmarks/security-noninterference-none-medium/input/Task.v.orig)与 trace 最初读取的输入逐字一致；最终证明文件保留了相同的语言定义和目标陈述。当前 [card.md](/data0/zzh/PL-Paper-AutoProof/benchmarks/security-noninterference-none-medium/card.md)的目标也与之相符，未发现会影响本次判断的题面差异。
