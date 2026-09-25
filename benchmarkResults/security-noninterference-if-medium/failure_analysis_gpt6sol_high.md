# security-noninterference-if-medium

Run tag: `gpt6sol_high`  
Recorded status: `timeout`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

主要瓶颈是**把逻辑关系的语义辅助引理整合成覆盖全部类型规则的基本定理**。证明需要同时处理擦除后的类型保持、求值形式转换、绑定变量代入，以及函数应用中的任意相关参数。这些准备工作和逐分支调试耗尽了 3600 秒；trace 没有显示 agent 已推进到 `if` 分支，因此不能把条件分支本身判为根因。

## 关键证据

- [运行结果](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-if-medium/results_gpt6sol_high.json)为 `timeout`，耗时 3600 秒；token 用量未记录。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-if-medium/traces_gpt6sol_high/security-noninterference-if-medium.jsonl)中，agent 先反复编译和修正擦除类型保持、代入、求值转换及逻辑关系传递等引理，到后段才开始 `fundamental_big_eval`。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-if-medium/proofs_gpt6sol_high/security-noninterference-if-medium.v:2330)只写到基本定理的变量、单位、抽象、应用和乘积构造分支，后续规则尚未覆盖；末尾的 `noninterference` 仍为 `Admitted`。最后一次编辑后，trace 中也没有成功编译记录。
- trace 开始时读取的 `Task.v` 与[当前原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/security-noninterference-if-medium/input/Task.v.orig)逐字一致；未发现应将当前输入与当时题面区分处理的变化。
