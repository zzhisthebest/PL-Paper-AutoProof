# systemf-refinement-soundness-recursion-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

**停在**由闭项精化类型 `has_rtype [] empty_rcontext t R` 推出 `evals_denotes R t`；最终的 `Qed` 因这一目标未完成而失败。

**主要原因**是运行 agent 没有建立贯穿各条精化类型规则的广义语义证明。它完成了若干闭项的求值与安全性引理，也证明了蕴含关系的一个辅助引理，但没有把上下文解释、代换和子类型关系接到类型推导上。递归函数的递减度量也是该证明必须处理的义务；trace 中没有对这一分支的实质证明尝试，因此**不能确定它是最难的单一分支**。证据更支持“整体证明框架未建立”，而非最后一个 tactic 报错导致失败。

## 关键证据

- [result](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-recursion-medium/results_gpt6sol_high.json) 记录状态为 `failed`。运行末尾的 [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-recursion-medium/traces_gpt6sol_high/systemf-refinement-soundness-recursion-medium.jsonl:165) 显示：辅助引理前缀编译成功，完整文件留下的唯一目标正是 `evals_denotes R t`。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-recursion-medium/proofs_gpt6sol_high/systemf-refinement-soundness-recursion-medium.v:1201) 定义了 `context_denotes`，但后续没有广义 fundamental theorem 或语义子类型证明；[目标定理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-recursion-medium/proofs_gpt6sol_high/systemf-refinement-soundness-recursion-medium.v:1662) 直接调用安全性引理，因而缺少其前提。
- 当前 [原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-recursion-medium/input/Task.v.orig) 的既有定义与最终证明文件前缀一致，题目目标也一致；未发现会改变本次判断的题面差异。trace 未保存当时卡片全文，无法逐字核对 [当前卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-recursion-medium/card.md)。
