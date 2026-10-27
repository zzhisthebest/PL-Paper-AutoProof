# Feature 倒挂分析：每题重复 20 次

比较 STLC Strong Normalization 的两道 Hard 题：004（+if）和 001（none）。每题独立运行 20 次，共 40 次。

- 模型：DeepSeek Flash（`deepseek-flash[1m]`）。
- Harness：Claude Code 2.1.308，effort 配置为 `max`。
- 预算：每次 3600 秒。
- 顺序：先并行运行 004 的 20 次，全部结束后再并行运行 001 的 20 次。
- 各次运行使用独立工作目录和会话，不提供 LR-first 提示。

`results.json` 汇总全部 40 次结果。各题目录下的 `r01` 至 `r20` 分别保存对应运行的 `proofs/Task.v` 和 `traces/`。

[六道题、120 次运行的证明代码与完整过程回放](proof-viewer.html)：下载 HTML 后用浏览器打开，可按功能分块对照最终代码，逐步回放 trace，并查看各次运行的问题与耗时。
