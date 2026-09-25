# systemf-refinement-soundness-if-nondeterminism-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

这次运行停在从封闭精化类型推导 `evals_denotes` 的基本定理。更具体地说，agent 没有建立能覆盖开放项的环境代入和语义子类型证明框架，因此已证明的整数、布尔值、选择和条件分支引理，无法接到函数、多态及 `RT_Sub` 等一般类型规则上。

**具体是哪一个主归纳分支最难，证据不足以确定。** Trace 中没有真正展开这项归纳；多次编译报错主要发生在辅助引理中，后来已修复，不能把那些 tactic 报错当作根因。

## 关键证据

- [result](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-medium/results_gpt6sol_high.json) 记录 `failed`、耗时 592 秒。最终 [Task.v](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-medium/proofs_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-medium.v:1339) 用 `never_stuck_from_fundamental` 收尾，却留下“所有封闭精化类型项满足 `evals_denotes`”这一完整前提；[trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-medium/traces_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-medium.jsonl:130) 显示的开放目标正是它。
- 最终文件只有一个[上下文解释定义](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-nondeterminism-medium/proofs_gpt6sol_high/systemf-refinement-soundness-if-nondeterminism-medium.v:1100)，没有环境代入、语义子类型或基本定理的证明。题目中的[函数与多态类型规则](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-nondeterminism-medium/input/Task.v.orig:873)涉及打开绑定体；[子类型规则](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-nondeterminism-medium/input/Task.v.orig:942)也需纳入整体论证。Trace 显示 agent 的工作集中在辅助语义引理，而未推进这些连接。
- Trace 开始时读取的 `Task.v` 与当前 `Task.v.orig` **逐字相同**，因此这里没有把改过的当前输入误当成当时题面。Trace 未记录读取 `card.md`，其历史文本无法逐字核验；当前卡片与已核验的输入及目标一致。
