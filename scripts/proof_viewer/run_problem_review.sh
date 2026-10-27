#!/usr/bin/env bash
# Review existing analyses. Keep originals and skip already reviewed runs.
set -euo pipefail
cd /data0/zzh/PL-Paper-AutoProof
source scripts/deepseek_cc_env.sh
export HTTPS_PROXY=http://127.0.0.1:20171
export HTTP_PROXY="$HTTPS_PROXY"
export https_proxy="$HTTPS_PROXY"
export http_proxy="$HTTP_PROXY"

status=0
python scripts/proof_viewer/review_problems.py --parallel 100 "$@" || status=$?
if [ "$status" -ne 130 ]; then
    python scripts/proof_viewer/build.py
fi
exit "$status"
