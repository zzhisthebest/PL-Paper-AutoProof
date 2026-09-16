#!/usr/bin/env bash
set -euo pipefail

cd /data0/zzh/PL-Paper-AutoProof

TAG="${TAG:-gpt56sol_high}"
MODEL="${MODEL:-gpt-5.6-sol}"
REASONING_EFFORT="${REASONING_EFFORT:-high}"
TIMEOUT="${TIMEOUT:-3600}"
PARALLEL="${PARALLEL:-100}"
EXPECTED_CASES="${EXPECTED_CASES:-96}"

mapfile -t BENCHMARKS < <(
  for benchmark_dir in benchmarks/*; do
    if [[ -f "$benchmark_dir/card.md" && -f "$benchmark_dir/input/Task.v" ]]; then
      basename "$benchmark_dir"
    fi
  done | sort
)

if [[ "${#BENCHMARKS[@]}" -ne "$EXPECTED_CASES" ]]; then
  echo "Expected $EXPECTED_CASES benchmark cases, found ${#BENCHMARKS[@]}." >&2
  exit 1
fi

echo "Running ${#BENCHMARKS[@]} cases with parallelism $PARALLEL."
echo "Model: $MODEL ($REASONING_EFFORT)"
echo "Tag:   $TAG"

export TAG MODEL REASONING_EFFORT TIMEOUT

printf '%s\0' "${BENCHMARKS[@]}" | xargs -0 -n 1 -P "$PARALLEL" bash -c '
  benchmark="$1"
  extra_args=()
  if [[ "$benchmark" == *-hard ]]; then
    extra_args+=(--lr-first)
  fi

  python scripts/test.py \
    --benchmark "$benchmark" \
    --tag "$TAG" \
    --model "$MODEL" \
    --reasoning-effort "$REASONING_EFFORT" \
    --timeout "$TIMEOUT" \
    "${extra_args[@]}"
' _
