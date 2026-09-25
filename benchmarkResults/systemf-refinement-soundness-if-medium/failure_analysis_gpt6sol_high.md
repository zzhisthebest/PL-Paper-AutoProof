# systemf-refinement-soundness-if-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

运行停在目标定理所需的桥梁：**从闭合精化类型推导得到 `evals_denotes`**。最终文件已经证明了“`evals_denotes` 蕴含可达状态不会卡住”，也证明了 if 的语义引理，但没有建立覆盖整个 `has_rtype` 的基本定理。

从规则看，这座桥梁需要处理函数与多态绑定中的打开和代换，以及 `RT_Sub` 所需的语义子类型证明。更有把握的能力判断是：agent 花了大量工作完成外围引理，却没有展开并验证这些核心归纳义务。trace 没有显示它反复尝试基本定理，因此**无法确定代换、类型变量还是子类型中的哪一项最难**。

## 关键证据

- [结果文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-medium/results_gpt6sol_high.json)记录 `failed`，耗时 538 秒。trace 中辅助引理的编译错误陆续得到修正；最后一次编译仍在 `never_stuck` 的 `Qed` 报“remaining open goals”。
- [最终证明](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-medium/proofs_gpt6sol_high/systemf-refinement-soundness-if-medium.v:1314)直接调用 `evals_denotes_reachable_progress`，却没有证明类型假设 `Htyping` 能给出该引理要求的 `evals_denotes`。文件中有 `context_denotes` 和 [if 引理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-medium/proofs_gpt6sol_high/systemf-refinement-soundness-if-medium.v:1287)，没有基本定理或语义子类型引理。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-medium/traces_gpt6sol_high/systemf-refinement-soundness-if-medium.jsonl)显示 agent 主要迭代确定性、终止到进展、值结果唯一性及 if 引理；没有针对上述核心归纳证明的实际失败目标可供进一步定位。
- trace 最初读取的 `Task.v` 与[当前原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-medium/input/Task.v.orig)逐字一致。当前卡片与该输入、最终证明的目标也一致；未发现题面不一致。
