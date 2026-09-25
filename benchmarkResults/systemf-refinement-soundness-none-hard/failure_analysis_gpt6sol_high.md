# systemf-refinement-soundness-none-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

证明停在从闭合的 `has_rtype` 判断推出 `expression_relation`。更具体的能力缺口是：agent 写出了求值与逻辑关系的若干局部引理，却没有建立**开放上下文中的基本定理**，把变量和类型变量的赋值、依赖精化中的替换，以及子类型和谓词蕴含规则接到这些引理上。

这不是最后一个 `Qed` 的 tactic 问题。trace 中没有对基本定理各分支的完整证明尝试，因此无法进一步确认究竟是绑定变量、存在类型子类型，还是谓词蕴含中的哪一类义务最难。

## 关键证据

- [结果文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-none-hard/results_gpt6sol_high.json)记为 `failed`。trace 最后显示唯一未解目标是 `expression_relation R [] [] t`，已知前提为 `has_rtype [] empty_rcontext t R`；[最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-none-hard/proofs_gpt6sol_high/systemf-refinement-soundness-none-hard.v:1474)也在此处结束。
- 最终文件证明了整数、除法、算术和应用等局部相容性，但除法与算术引理只针对空环境；`context_relation` 虽已定义，尚无引理将它与 `has_rtype` 的归纳规则连接。子类型方面仅有反身、传递及有条件的函数和多态相容性引理，尚未处理精化蕴含、存在见证等规则。这些都是建立开放上下文基本定理时需要跨过的接口。
- [trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-none-hard/traces_gpt6sol_high/systemf-refinement-soundness-none-hard.jsonl)显示 agent 持续修复并编译局部引理，末尾才留下上述基本定理目标；不能把其最终自述当成某一具体分支已被反复尝试且失败的证据。
- 当前 [Task.v.orig](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-none-hard/input/Task.v.orig)与 trace 中读取的原始输入逐字一致，目标定理也一致。[card.md](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-none-hard/card.md)未在 trace 中被读取，无法核实其全文当时是否相同；目前未发现影响本次判断的题面差异。
