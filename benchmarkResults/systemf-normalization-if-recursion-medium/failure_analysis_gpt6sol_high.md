# systemf-normalization-if-recursion-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

**证明停在 `normalization`，主要瓶颈则是尚未建立贯穿项绑定与类型绑定的语义替换框架。** 已完成的引理处理了 `if`、应用、类型应用和自然数递归的求值相容性；但从 `has_type` 的归纳假设走到这些引理，还需要处理新鲜变量、打开绑定体、替换交换，以及类型替换与关系环境的对应。尤其在 `T_Abs` 和 `T_TAbs` 分支，这些义务不能直接由现有相容性引理推出。

trace 没有展示 agent 对 fundamental theorem 的这些分支进行实际证明尝试，因此**无法确认某一条具体替换引理是唯一根因**。较稳妥的判断是：运行把时间用在局部求值引理上，未能构造并验证所需的整体归纳不变量。

## 关键证据

- [结果文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-normalization-if-recursion-medium/results_gpt6sol_high.json)记录状态为 `failed`，耗时 859 秒。
- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-normalization-if-recursion-medium/proofs_gpt6sol_high/systemf-normalization-if-recursion-medium.v:908)中，相容性引理已有 `Qed`，但 `normalization` 的证明体仍只有占位注释；[trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-normalization-if-recursion-medium/traces_gpt6sol_high/systemf-normalization-if-recursion-medium.jsonl)最后一次编译报的是该定理存在未关闭目标，而非递归或应用引理报错。
- 原有 `related_substitution` 只描述项替换，没有把类型替换与关系环境关联起来；trace 多次转向替换和新鲜变量问题，最终没有写入相应引理。这支持上述瓶颈判断，但不是某个具体分支失败的直接记录。
- trace 开始时读取的原始 `Task.v` 与[当前 `Task.v.orig`](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-normalization-if-recursion-medium/input/Task.v.orig)逐字一致；未发现当前输入与运行时题面不一致。
