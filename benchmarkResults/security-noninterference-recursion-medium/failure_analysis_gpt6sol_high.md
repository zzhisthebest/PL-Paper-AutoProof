# security-noninterference-recursion-medium

Run tag: `gpt6sol_high`  
Recorded status: `timeout`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

主要瓶颈是**把已建立的类型、替换和求值辅助引理接成逻辑关系的基本定理**。证明实际停在函数抽象分支：需要将合式性证明中“用新变量打开函数体”的前提，转成函数应用时“用相关实参替换函数体”的关系证明。运行结束时，这一分支仍未闭合，其余大多数归纳分支也尚未处理。最后的 tactic 报错只是当时的编译阻点，不能单独解释超时。

递归分支尚未进入，因此**没有证据认定自然数递归证明本身是主要瓶颈**。

## 关键证据

- [result](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-recursion-medium/results_gpt6sol_high.json) 记录为 3600 秒超时。trace 曾显示基本定理有 15 个归纳目标；接近结束时仍在函数抽象目标中处理新变量、环境更新与 `close_term_open_update`。
- [最终证明](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/security-noninterference-recursion-medium/proofs_gpt6sol_high/security-noninterference-recursion-medium.v:2008) 已有大量辅助引理，包括擦除后的类型保持、替换和大小步求值桥接；但 `fundamental_low_lifting` 与 `noninterference` 均以 `Admitted` 结束。最后一次 `coqc` 在函数抽象分支第 2052 行失败，文件当时也未通过编译。
- 当前 [Task.v.orig](/data0/zzh/PL-Paper-AutoProof/benchmarks/security-noninterference-recursion-medium/input/Task.v.orig) 与 trace 所示的 493 行起始输入、最终证明保留的原定义和目标陈述一致。当前 card 的目标陈述也一致；trace 未保存当时 card 全文，无法核实措辞是否曾变化。
