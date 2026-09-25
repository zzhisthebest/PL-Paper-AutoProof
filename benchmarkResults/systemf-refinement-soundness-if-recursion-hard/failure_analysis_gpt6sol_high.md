# systemf-refinement-soundness-if-recursion-hard

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

**未能把已定义的逻辑关系接到原有判型规则上。** 运行证明了除法安全性等局部引理，却没有建立“精化类型判型蕴含相关项”的基本定理。具体缺口集中在带依赖精化的开项与封闭代换、环境扩展，以及谓词语义之间的对应关系；这些关系缺失时，局部引理无法覆盖任意良型程序。递归调用还需要下降度量的论证，但 trace 中没有形成可检验的递归案例证明，因此**不能确定它比代换问题更主要**。

## 关键证据

- [结果](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-recursion-hard/results_gpt6sol_high.json)记为 `failed`。最终[证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-recursion-hard/proofs_gpt6sol_high/systemf-refinement-soundness-if-recursion-hard.v:1564)中的 `never_stuck` 仍是空证明；最后编译报“remaining open goals”。这是**停点**，不是单凭该报错推断的根因。
- 最终文件定义了 `close_tm_rec`、`close_formula` 和 `related_value`，也证明了除法安全性；但没有证明判型到逻辑关系的连接引理。例如，[环境精化引理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-recursion-hard/proofs_gpt6sol_high/systemf-refinement-soundness-if-recursion-hard.v:1449)给出 `close_formula` 下的谓词成立，而[蕴含语义引理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-if-recursion-hard/proofs_gpt6sol_high/systemf-refinement-soundness-if-recursion-hard.v:1551)使用 `instantiate_formula`；两者所需的对应证明并未出现。trace 后段仍在加强环境假设、查看归纳原理，没有进入完整的判型归纳。
- 版本核对：当前[原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-recursion-hard/input/Task.v.orig)与最终证明文件的原题部分一致，trace 开始时的输入也记录为同样的 1155 行、42299 字节，未发现题面冲突。[当前卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-if-recursion-hard/card.md)在 trace 中仅有文件大小记录，无法独立确认其当时内容。
