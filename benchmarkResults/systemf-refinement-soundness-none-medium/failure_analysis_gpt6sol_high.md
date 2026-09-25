# systemf-refinement-soundness-none-medium

Run tag: `gpt6sol_high`  
Recorded status: `failed`  
Analysis model: `gpt-6-sol` (high)

## 主要瓶颈

证明**停在**空白的 `never_stuck`，但这只是最终表现。更主要的瓶颈是：agent 完成了若干局部求值和指称引理后，没有建立贯穿整个精化类型推导的基本定理。现有的环境解释只处理项变量；要覆盖函数与多态绑定、开项的封闭替换，以及蕴含和子类型规则，还需要一套相互配合的语义替换引理。

这是从缺失的证明结构作出的判断。trace **没有显示** agent 反复尝试基本定理中的某一个具体分支，因此无法确认究竟是哪条绑定或子类型规则最难攻克。

## 关键证据

- [结果](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-none-medium/results_gpt6sol_high.json)记录为 `failed`，耗时 771 秒；[最终证明文件](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-none-medium/proofs_gpt6sol_high/systemf-refinement-soundness-none-medium.v:1519)中的 `never_stuck` 仍为空证明。
- 最终文件已有[环境解释](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-none-medium/proofs_gpt6sol_high/systemf-refinement-soundness-none-medium.v:1244)及除法、算术、应用的指称引理，却没有基本定理，也没有蕴含或子类型保持指称的证明。[trace](/data0/zzh/PL-Paper-AutoProof/benchmarkResults/systemf-refinement-soundness-none-medium/traces_gpt6sol_high/systemf-refinement-soundness-none-medium.jsonl:182)最后再次编译时，报错仍是目标证明存在未关闭的子目标；此前辅助引理的多次 tactic 报错并非最终阻碍。
- 当前 [Task.v.orig](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-none-medium/input/Task.v.orig:1015)为 1026 行，与 trace 开始时读取的行数一致，且与最终文件新增证明之前的内容一致。当前[题目卡片](/data0/zzh/PL-Paper-AutoProof/benchmarks/systemf-refinement-soundness-none-medium/card.md)也与运行中处理的任务相符；未发现需要将当前题面与当时题面区分开的冲突。
