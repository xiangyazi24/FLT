#!/usr/bin/env bash
set -euo pipefail
ROOT=/workspace/shared/flt-n25-weighted-reindexing
export LEAN_PATH="$ROOT/check_project"
for name in N25F_ExactCountWeightedSum N25F_ExactCountQuotientDegree; do
  cmp "$ROOT/$name.lean" "$ROOT/check_project/FLT/Assumptions/MazurProof/$name.lean"
  python "$ROOT/run_check.py" "$name-final" -R "$ROOT/check_project" \
    -o "$ROOT/check_project/FLT/Assumptions/MazurProof/$name.olean" \
    "$ROOT/check_project/FLT/Assumptions/MazurProof/$name.lean"
done
python "$ROOT/run_check.py" audit-final "$ROOT/ExactCountAudit.lean"
