# systemf-refinement-soundness-if-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

证明停在 `never_stuck` 所需的 `fundamental_property`：最终文件只**定义**了基本定理命题，没有证明它。主要瓶颈是把已完成的局部安全性引理，提升为覆盖全部精化类型规则和子类型规则的归纳证明；其中需要协调项与类型绑定变量、闭合替换、上下文扩展及子类型语义。

trace 没有展示基本定理在某个具体分支上反复失败，因此**无法确定** `RT_Abs`、`S_Bind` 等哪一条规则是决定性的难点。

## 关键证据

- [运行结果](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-hard/results_gpt6sol_high.json) 为 `failed`，耗时 1527 秒。
- [最终证明](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-hard/proofs_gpt6sol_high/systemf-refinement-soundness-if-hard.v:1802) 已有除法、算术、应用和条件表达式等局部引理；但 `never_stuck` 在 [第 1909 行](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-hard/proofs_gpt6sol_high/systemf-refinement-soundness-if-hard.v:1909) 调用收尾引理时，仍须提供未证明的 `fundamental_property`。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-hard/traces_gpt6sol_high/systemf-refinement-soundness-if-hard.jsonl) 的最后检查显示唯一剩余目标正是 `fundamental_property`；编译在 `Qed` 处因开放目标失败。这说明报错是停点，不足以单独解释深层原因。
- 当前 [card](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-hard/card.md) 与 trace 中读取的卡片一致；当前 [原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-hard/input/Task.v.orig) 的语言定义部分与最终证明前缀一致，未发现题面变更造成的误判。
