#!/usr/bin/env bash
set -euo pipefail

cd /data0/zzh/PL-Paper-AutoProof

TAG="${TAG:-gpt56sol_high_lrfirst}"
BENCHMARK="${BENCHMARK:-systemf}"
MODEL="${MODEL:-gpt-5.6-sol}"
REASONING_EFFORT="${REASONING_EFFORT:-high}"
TIMEOUT="${TIMEOUT:-1800}"

python scripts/test.py \
  --benchmark "$BENCHMARK" \
  --tag "$TAG" \
  --model "$MODEL" \
  --reasoning-effort "$REASONING_EFFORT" \
  --lr-first \
  --timeout "$TIMEOUT"
