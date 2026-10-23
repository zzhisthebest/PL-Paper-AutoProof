#!/usr/bin/env bash
# 倒挂分析：先跑 004（+if），再跑 001（none），每题独立重复 20 次。
set -euo pipefail
cd /data0/zzh/PL-Paper-AutoProof

# 仅为本次脚本运行配置模型和代理，不修改永久配置。
source scripts/deepseek_cc_env.sh
export HTTPS_PROXY=http://127.0.0.1:20171
export HTTP_PROXY="$HTTPS_PROXY"

TAG=deepseek_flash_claude_code_feature_inversion_3600s
TIMEOUT=3600

# 外层循环控制题目顺序。
for CASE in 004 001; do
  echo "开始题目 $CASE：20 次并行，每次 $TIMEOUT 秒"

  # & 表示后台运行，因此这 20 次会并行执行。
  # 每次使用不同的 tag，分别保存结果；工作目录和会话也相互独立。
  for REPEAT in {01..20}; do
    python scripts/test.py \
      --benchmark "$CASE" \
      --tag "${TAG}_r${REPEAT}" \
      --timeout "$TIMEOUT" \
      --reject-admits &
  done

  # 等当前题目的 20 次运行全部结束，再进入下一道题。
  wait
  echo "题目 $CASE 的 20 次运行已结束"
done
