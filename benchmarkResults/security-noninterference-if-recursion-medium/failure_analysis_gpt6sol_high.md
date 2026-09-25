# security-noninterference-if-recursion-medium

Run tag: `gpt6sol_high`  
Recorded status: `timeout`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

主要瓶颈是**组织并完成逻辑关系基本定理的组合证明**。运行 agent 在局部无名变量的开项、环境闭包和类型保持引理上反复修补；完成这些准备后，仍未建立函数应用等消去式所需的“双侧求值结果相关、再施加安全保护”的引理。证明**停在** `fundamental_low` 的函数应用分支，但这只是未完成证明的当前位置；trace 没有显示它反复尝试 `if` 或自然数递归分支，因此不能把根因具体归为递归证明失败。

## 关键证据

- [结果记录](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-if-recursion-medium/results_gpt6sol_high.json) 为运行 3600 秒后超时。trace 中反复编译、修补 `typing_close_env` 和 `lc_open_to_body` 一带的证明义务；后者多次出现未关闭的目标。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-if-recursion-medium/proofs_gpt6sol_high/security-noninterference-if-recursion-medium.v:1921) 的 `fundamental_low` 只处理了变量、unit 和抽象。最后一次[编译输出](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-if-recursion-medium/traces_gpt6sol_high/security-noninterference-if-recursion-medium.jsonl:635) 显示函数应用分支仍有目标，`Qed` 因此失败；目标定理随后仍是 [`Admitted`](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-if-recursion-medium/proofs_gpt6sol_high/security-noninterference-if-recursion-medium.v:1978)。
- trace 开头读取的 `Task.v` 与[当前原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/security-noninterference-if-recursion-medium/input/Task.v.orig) **逐字相同**；[当前卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/security-noninterference-if-recursion-medium/card.md) 所列目标也与文件中的定理一致。未发现可确认的题面版本差异。
