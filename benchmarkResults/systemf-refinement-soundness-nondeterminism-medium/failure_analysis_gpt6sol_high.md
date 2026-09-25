# systemf-refinement-soundness-nondeterminism-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

主要瓶颈是**没有建立从精化类型推导到闭合程序语义性质的通用证明**。最终定理已化简为 `has_rtype [] empty_rcontext t R -> evals_denotes R t`，但文件中只有整数、选择和除数非零等局部引理；尚无把上下文中的开放项闭合、处理绑定与类型实例化、并证明子类型保持语义的引理。

这说明证明停在类型系统与逻辑关系的衔接处。trace 没有实际展开通用证明的各个构造，因此**无法确认某一个具体构造反复受阻**；绑定和子类型是从缺失的证明结构推断出的主要难点，不能仅凭运行 agent 的自述断定。

## 关键证据

- [result](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-medium/results_gpt6sol_high.json) 记录 `failed`，耗时 736 秒。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-medium/proofs_gpt6sol_high/systemf-refinement-soundness-nondeterminism-medium.v:1046) 定义了 `context_interpretation`，却没有闭合替换或通用 fundamental theorem；[定理末尾](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-medium/proofs_gpt6sol_high/systemf-refinement-soundness-nondeterminism-medium.v:1203) 直接调用安全性引理，留下上述语义前提。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-medium/traces_gpt6sol_high/systemf-refinement-soundness-nondeterminism-medium.jsonl:125) 显示该前提仍是开放目标。运行过程多次修正局部引理的证明脚本，未见对完整 `has_rtype` 推导或 `subtype` 的语义归纳证明。
- 当前 [card](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-nondeterminism-medium/card.md) 与 trace 中读取的题目卡片一致；当前 [原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-nondeterminism-medium/input/Task.v.orig) 与最终文件在任务模块之前一致，未发现题面版本差异。
