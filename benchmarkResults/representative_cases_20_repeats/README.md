# 代表性任务：每题重复 20 次

4 道 Hard 题，每题独立运行 20 次，共 80 次。每题内部 20 次并行，不同题目依次运行。

| 编号 | 任务 | Feature |
|---|---|---|
| 034 | System F strong normalization | Recursion |
| 055 | System F polymorphic identity | Nondeterminism |
| 073 | System F refinement type safety | None |
| 100 | Secure STLC noninterference | If |

模型为 DeepSeek Flash，harness 为 Claude Code 2.1.308；每次总时间预算 3600 秒，未启用 lr-first。
续跑保留原会话和证明文件，不重置时间预算。034 运行时续跑提示包含剩余时间，后续运行前已移除该提示。

## 文件

- `results.json`：合并的 80 条原始结果，包含题号、重复编号、状态、耗时、用量及文件相对路径；未重新计算指标。
- `<case>/r01/` 至 `r20/`：各次运行的 `proofs/Task.v`、`traces/*.jsonl.gz` 和 stderr 日志。Trace 使用 gzip 无损压缩，可用 `gzip -dc 文件.jsonl.gz` 读取。
- `raw_results/`：保留整理前按 tag 保存的结果文件。

本目录仅归档运行记录，尚未分析结果。
