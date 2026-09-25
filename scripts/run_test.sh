#!/usr/bin/env bash
set -euo pipefail

cd /data0/zzh/PL-Paper-AutoProof

BACKEND="${BACKEND:-codex}"
if [[ "$BACKEND" == "qwen" ]]; then
  TAG="${TAG:-qwen38_27b_high}"
  MODEL="${MODEL:-qwen3.8-27b-local}"
  PARALLEL="${PARALLEL:-6}"
else
  TAG="${TAG:-gpt6sol_high}"
  MODEL="${MODEL:-gpt-6-sol}"
  PARALLEL="${PARALLEL:-72}"
fi
REASONING_EFFORT="${REASONING_EFFORT:-high}"
TIMEOUT="${TIMEOUT:-3600}"
QWEN_START_PORT="${QWEN_START_PORT:-8200}"

if [[ "$BACKEND" != "codex" && "$BACKEND" != "qwen" ]]; then
  echo "BACKEND must be codex or qwen, got: $BACKEND" >&2
  exit 2
fi

if [[ "$BACKEND" == "qwen" ]]; then
  if (( PARALLEL < 1 || PARALLEL > 6 )); then
    echo "Qwen parallelism must be between 1 and 6, got: $PARALLEL" >&2
    exit 2
  fi
  for offset in $(seq 0 $((PARALLEL - 1))); do
    port=$((QWEN_START_PORT + offset))
    if ! curl --noproxy '*' -fsS "http://127.0.0.1:$port/v1/models" >/dev/null; then
      echo "Qwen endpoint on port $port is not ready." >&2
      exit 1
    fi
  done
fi

BENCHMARKS=()
for card in benchmarks/*/card.md; do
  benchmark="${card#benchmarks/}"
  benchmark="${benchmark%/card.md}"
  if [[ "$benchmark" == *-medium || "$benchmark" == *-hard ]]; then
    BENCHMARKS+=("$benchmark")
  fi
done

if (( ${#BENCHMARKS[@]} != 72 )); then
  echo "Expected 72 Medium/Hard cases, found ${#BENCHMARKS[@]}." >&2
  exit 1
fi

for benchmark in "${BENCHMARKS[@]}"; do
  if [[ ! -f "benchmarks/$benchmark/card.md" ||
        ! -f "benchmarks/$benchmark/input/Task.v" ]]; then
    echo "Benchmark is missing: $benchmark" >&2
    exit 1
  fi
done

echo "Running ${#BENCHMARKS[@]} cases with parallelism $PARALLEL."
echo "Backend: $BACKEND"
echo "Model: $MODEL ($REASONING_EFFORT)"
echo "Tag:   $TAG"

export TAG MODEL REASONING_EFFORT TIMEOUT BACKEND QWEN_START_PORT

printf '%s\0' "${BENCHMARKS[@]}" | xargs -0 -n 1 -P "$PARALLEL" \
  --process-slot-var=WORKER_SLOT bash -c '
  benchmark="$1"
  extra_args=()
  if [[ "$benchmark" == *-hard ]]; then
    extra_args+=(--lr-first)
  fi
  if [[ "$BACKEND" == "qwen" ]]; then
    port=$((QWEN_START_PORT + WORKER_SLOT))
    extra_args+=(--local-base-url "http://127.0.0.1:$port/v1")
  fi
  python scripts/test.py \
    --benchmark "$benchmark" \
    --tag "$TAG" \
    --model "$MODEL" \
    --reasoning-effort "$REASONING_EFFORT" \
    --timeout "$TIMEOUT" \
    "${extra_args[@]}"
' _
