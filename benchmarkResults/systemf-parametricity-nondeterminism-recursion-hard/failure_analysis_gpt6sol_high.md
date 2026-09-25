# systemf-parametricity-nondeterminism-recursion-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

**停在哪：**最终定理还缺一个关键前提：从 `t` 的闭合类型推导，证明 `t` 与自身满足二元逻辑关系。运行以 `failed` 结束，最终文件在定理的 `Qed` 处仍有一个目标。

**为什么停在那里：**agent 证明了选择、递归、应用等局部关系引理，也补了闭合性与替换、打开操作的交换引理，但没有建立覆盖**两侧类型与项替换**的基本定理。它定义了类型和项上下文的解释，却未将这些定义接入按类型推导的归纳证明；函数抽象和类型抽象所需的关系传递因此没有完成。trace 没有展示逐个尝试并卡在某一个抽象分支，所以不能进一步断言是哪一个分支单独造成失败。

## 关键证据

- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-parametricity-nondeterminism-recursion-hard/proofs_gpt6sol_high/systemf-parametricity-nondeterminism-recursion-hard.v:920)有上下文解释和辅助引理，但没有基本定理；[目标证明](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-parametricity-nondeterminism-recursion-hard/proofs_gpt6sol_high/systemf-parametricity-nondeterminism-recursion-hard.v:1177)直接调用 `identity_from_relation`。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-parametricity-nondeterminism-recursion-hard/traces_gpt6sol_high/systemf-parametricity-nondeterminism-recursion-hard.jsonl:340)显示剩余目标正是 `may_related ... t t`；最后补充替换交换引理后，`coqc` 仍在定理的 `Qed` 报未完成。
- [当前原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-parametricity-nondeterminism-recursion-hard/input/Task.v.orig:390)与最终文件的语言定义前缀、目标定理陈述一致；未发现当前[题目卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-parametricity-nondeterminism-recursion-hard/card.md)与这次运行题面有实质差异。
