#!/usr/bin/env bash
# Bounded, offline-after-setup Lean elaboration against the accepted FLT Mathlib pin.
set -euo pipefail
ROOT=/workspace/shared/lean-feedback
export PATH="$ROOT/lean-4.31.0-rc2-linux/bin:$PATH"
export LEAN_NUM_THREADS=1 MATHLIB_CACHE_DIR="$ROOT/cache"
CPU=$(awk '/Cpus_allowed_list/ {split($2,a,",|-"); print a[1]}' /proc/self/status)
cd "$ROOT/mathlib"
exec timeout --signal=TERM --kill-after=5s 60s taskset -c "$CPU" lake env lean -j 1 -M 3072 "$@"
