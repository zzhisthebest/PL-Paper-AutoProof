# systemf-refinement-soundness-if-nondeterminism-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

**证明停在从精化类型推导到语义关系的桥梁。** 最终的 `never_stuck` 只调用了语义安全引理，却没有从 `has_rtype` 证明其所需的 `semantic_type`，因此 `Qed` 留有未解目标。

更具体地看，agent 反复处理的是**闭合性，以及局部无名表示下的打开与替换**：它为选择、除法、条件和算术补闭合条件，又补了一条打开与替换交换的引理；但没有把这些局部引理组织成适用于开放项、环境扩展和子类型规则的归纳证明。trace 未显示它实际推进完整的类型／子类型归纳，因此**无法确认究竟是哪一个绑定或子类型分支最难**。

## 关键证据

- [结果记录](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-hard/results_gpt6sol_high.json) 为 `failed`；[trace 末尾](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-hard/traces_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-hard.jsonl:248) 的编译输出明确报 `never_stuck` 证明未完成。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-hard/proofs_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-hard.v:1623) 中，目标证明没有使用 `Htyped` 来建立 `semantic_type`；已定义的 `context_relation`、闭合替换函数也未进入该证明。
- trace 显示 agent 曾因算术精化所需的闭合性强化语义关系，并尝试证明打开与替换交换；这些前置工作完成后，仍只剩上述全局桥梁。当前 [input](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-nondeterminism-hard/input/Task.v.orig:1000) 与 trace 中运行初始文件的大小、目标及最终文件的原有部分一致，未发现题面变更影响此判断。
