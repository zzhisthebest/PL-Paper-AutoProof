#!/usr/bin/env bash
set -euo pipefail

cd /data0/zzh/PL-Paper-AutoProof

TAG="${TAG:-gpt56sol_high_medium_lr_reconstruction_1800}"
MODEL="gpt-5.6-sol"
REASONING_EFFORT="high"
TIMEOUT=1800
PARALLEL=4

BENCHMARKS=(
  stlc-normalization-recursion-medium
  systemf-normalization-none-medium
  systemf-parametricity-none-medium
  systemf-refinement-soundness-none-medium
)

for benchmark in "${BENCHMARKS[@]}"; do
  for file in card.md input/Task.v input/Task.v.orig; do
    if [[ ! -f "benchmarks/$benchmark/$file" ]]; then
      echo "Missing input: benchmarks/$benchmark/$file" >&2
      exit 1
    fi
  done
done

echo "Running ${#BENCHMARKS[@]} Medium LR-reconstruction cases in parallel."
echo "Model: $MODEL ($REASONING_EFFORT); timeout: ${TIMEOUT}s per attempt."
echo "Tag: $TAG"

export TAG MODEL REASONING_EFFORT TIMEOUT

printf '%s\0' "${BENCHMARKS[@]}" | xargs -0 -n 1 -P "$PARALLEL" bash -c '
  python scripts/test.py \
    --benchmark "$1" \
    --tag "$TAG" \
    --model "$MODEL" \
    --reasoning-effort "$REASONING_EFFORT" \
    --timeout "$TIMEOUT"
' _
