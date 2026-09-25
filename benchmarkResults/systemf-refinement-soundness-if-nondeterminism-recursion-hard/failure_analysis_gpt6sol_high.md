# systemf-refinement-soundness-if-nondeterminism-recursion-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

运行停在空白的 `never_stuck` 证明；更主要的能力瓶颈是**没有把已建立的语义关系推进为覆盖精化类型与子类型规则的 fundamental theorem**。trace 中反复修补的是这一步所需的前置义务：归约上下文的局部闭合、谓词蕴涵，以及绑定变量实例化时必须使用闭值的不变量。最终只完成了整数、变量、选择和布尔 `if` 等局部引理。

函数、存在类型和多态类型涉及 opening 与语义替换的衔接；递归规则还涉及递减度量。这些是从[题目规则](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-nondeterminism-recursion-hard/input/Task.v.orig:1010)可见的剩余证明义务。但 trace 没有实际展开完整 fundamental theorem 的各分支，**无法确认其中哪一类分支是决定性的单一根因**，尤其不能仅凭 agent 的自述认定递归是主因。

## 关键证据

- [result](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-recursion-hard/results_gpt6sol_high.json)记录 `failed`，耗时 1089 秒。最后一次编译报错仍是 `never_stuck` 有未解决目标；[最终文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-recursion-hard/proofs_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-recursion-hard.v:1607)中该证明体确为空白。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-recursion-hard/traces_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-recursion-hard.jsonl:127)显示 agent 中途发现闭值不变量缺失并加强语义关系；此前也多次编译、修补局部闭合与蕴涵引理。最终文件有安全性提取和局部相容性引理，却没有 fundamental theorem。
- 当前 `Task.v.orig` 与 trace 开始时读取的 1178 行逐行一致，最终文件也只在原输入之后增补内容。当前 card 的目标与运行一致；trace 未保存当时 card 的全文，无法核实它是否逐字相同。
