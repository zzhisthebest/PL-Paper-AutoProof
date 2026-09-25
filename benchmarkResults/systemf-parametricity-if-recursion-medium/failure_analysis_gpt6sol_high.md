# systemf-parametricity-if-recursion-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

**最可能的瓶颈是没有建立“类型推导蕴含逻辑关系”的基本定理所需的替换归纳框架。** 最后停在目标定理的空证明处，但这只是表现：已有引理能够从参数性推出目标结论，缺的是从 `has_type` 获得该参数性前提。具体难点集中在项抽象和类型抽象的绑定情形：需要把对新鲜变量打开后的类型推导，接到对任意相关值或关系候选的实例化上。

trace 多次规划项、类型替换及打开引理，却没有实际写出基本定理并检验其绑定情形。因此，这一瓶颈是由缺失的证明结构和工作轨迹支持的判断；**不能确定究竟是哪一条替换引理最终无法证明**。

## 关键证据

- [最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-parametricity-if-recursion-medium/proofs_gpt6sol_high/systemf-parametricity-if-recursion-medium.v:905) 已证明“给定 `expression_relation` 则推出目标”；[目标定理](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-parametricity-if-recursion-medium/proofs_gpt6sol_high/systemf-parametricity-if-recursion-medium.v:931) 仍为空。trace 的最后一次编译只在保存该空证明时报告未完成目标。
- 文件中已有应用、`if`、后继和原始递归的关系引理，但没有贯穿 `has_type` 各构造子的基本定理，也没有完成抽象及类型抽象所需的替换证明。[运行 trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-parametricity-if-recursion-medium/traces_gpt6sol_high/systemf-parametricity-if-recursion-medium.jsonl:160) 在结束前仍停留于规划替换映射。
- 当前 [原始输入](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-parametricity-if-recursion-medium/input/Task.v.orig:492) 与 trace 首次读取的运行时输入逐字一致；它的目标陈述也与最终证明文件一致。[当前卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-parametricity-if-recursion-medium/card.md) 的目标描述与之相符，未见题面变更证据。
