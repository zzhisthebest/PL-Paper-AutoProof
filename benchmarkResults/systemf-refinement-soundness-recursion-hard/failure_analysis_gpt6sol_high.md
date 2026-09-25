# systemf-refinement-soundness-recursion-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

主要瓶颈是**把局部的语义引理接成覆盖 refinement typing 与 subtyping 全部规则的 fundamental theorem**。尤其是带绑定变量的规则：需要把 cofinite 前提转成闭合替换后的实例，并证明扩展后的语义环境仍满足上下文中的 refinement。运行中持续补充 opening、替换和新鲜变量引理，但始终没有建立覆盖这些规则的归纳证明。具体是哪一条规则最终最难，现有 trace 不足以确定；不能仅凭最终报错归因于递归规则。

## 关键证据

- [结果](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-recursion-hard/results_gpt6sol_high.json) 标记为 `failed`；[trace 末尾](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-recursion-hard/traces_gpt6sol_high/systemf-refinement-soundness-recursion-hard.jsonl:209) 的编译错误是 `never_stuck` 的 `Qed` 尚有开放目标。
- [最终证明](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-recursion-hard/proofs_gpt6sol_high/systemf-refinement-soundness-recursion-hard.v:1737) 已证明从“所有 fuel 下满足 `semantic_term`”推出安全性，却没有证明 `has_rtype` 能给出这个前提；目标定理只调用了前者。因此，停在 `Qed` 是缺少 fundamental theorem 的表现，不是该 tactic 本身的问题。
- trace 后半段反复处理 `instantiate_open_body`、`instantiate_open_rty_body`、自由变量与新鲜变量引理；[最终文件相应部分](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-recursion-hard/proofs_gpt6sol_high/systemf-refinement-soundness-recursion-hard.v:1112) 也只形成了这些桥接引理和若干单独语义情形，没有 typing/subtyping 的完整归纳证明。trace 曾转向语义环境扩展、`RT_App`、类型实例化及绑定转换，但没有留下可定位为某一个规则失败的完整证明尝试。
- [当前 input](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-recursion-hard/input/Task.v.orig) 的原始 1097 行与最终证明对应部分一致；trace 起始时的文件也是 1097 行。[当前 card](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-recursion-hard/card.md) 所列目标与 trace、proof 一致。未发现会改变本次判断的题面差异。
