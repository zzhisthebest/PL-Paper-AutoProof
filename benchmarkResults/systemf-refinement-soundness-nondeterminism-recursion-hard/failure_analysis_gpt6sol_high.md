# systemf-refinement-soundness-nondeterminism-recursion-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

主要瓶颈是**未能把局部语义引理组成覆盖 `has_rtype` 与 `subtype` 的基本定理**。证明停在从闭合精化类型推导出“对所有步数都满足逻辑关系”这一步。现有引理处理了整数、除法的非零条件和选择分支，但尚未建立绑定变量的打开与替换、函数和存在类型、子类型以及度量递归所需的通用归纳论证。

trace 没有展示对这些复杂规则逐一展开后反复失败的过程，因此**无法确定其中哪一个规则是决定性的单点障碍**；能确认的是，局部引理始终没有接成完整的基本定理。

## 关键证据

- [运行结果](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-recursion-hard/results_gpt6sol_high.json) 标记为 `failed`，耗时 644 秒。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-recursion-hard/proofs_gpt6sol_high/systemf-refinement-soundness-nondeterminism-recursion-hard.v:1379) 定义了 `fundamental_property`，随后只证明变量、整数两个基本情形及选择引理；目标定理处的 `eauto` 仍需上述全称逻辑关系。[trace 最终编译记录](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-nondeterminism-recursion-hard/traces_gpt6sol_high/systemf-refinement-soundness-nondeterminism-recursion-hard.jsonl:129) 显示 `Qed` 时仍有未解决目标。
- trace 中步数索引定义和若干辅助证明曾报错，之后均被修正；除法非零与选择引理也已通过。因此最后的报错本身不是这些局部义务反复失败的证据。
- [当前原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-nondeterminism-recursion-hard/input/Task.v.orig) 的原有定义与最终文件对应部分一致，目标定理也一致。[当前卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-nondeterminism-recursion-hard/card.md) 的目标与之相符；trace 没有保存卡片原文，无法核实其措辞是否曾改动。
