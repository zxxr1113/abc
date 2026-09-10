#!/usr/bin/env bash
# Approved TFO + complete-observation baseline (fast35 Build mean 6.711162%).
# ABC, AIG_DIR, TIMEOUT, LIMIT, worker counts and SKIP_DSEC use the common runner.
# Algorithm settings are fixed here; use run_bench_parallel.sh for experiments.
set -euo pipefail
SCRIPT_DIR="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"
export STRAN_ARGS='-P root -F 1 -C 1000 -b 100 -S -1 -N 20 -B 16 -T 8 -D 1 -K 8 -Q 4 -W 8 -q 20 -j 5 -w 8 -V 0 -E 747118613 -d -k -J -O 0 -L 16 -p'
export SCORR_ARGS='-F 1 -C 1000'
export ABC_CEX_MODE=2 ABC_CEX_COMPRESS=4 ABC_CEX_PACK_FAST=2
export ABC_CEX_PROJECT_ALL=0
exec bash "$SCRIPT_DIR/run_bench_parallel.sh" "$@"
