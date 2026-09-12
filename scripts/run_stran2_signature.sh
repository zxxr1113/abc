#!/usr/bin/env bash
# Signature-guided version of the approved full-observation ODC preset.
# Modes: 0=control, 1=64 auxiliary samples, 2=also missing-value SAT,
# 3=also observed aliases (may lose valid sequential don't-care candidates).
set -euo pipefail
SCRIPT_DIR="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"
SIGNATURE_GUIDE_MODE="${SIGNATURE_GUIDE_MODE:-2}"
case "$SIGNATURE_GUIDE_MODE" in
    0|1|2|3) ;;
    *) echo 'ERROR: SIGNATURE_GUIDE_MODE must be 0, 1, 2 or 3' >&2; exit 1 ;;
esac
export STRAN_ARGS="-P root -F 1 -C 1000 -b 100 -S -1 -N 20 -B 16 -T 8 -D 1 -K 8 -Q 4 -W 8 -q 20 -j 5 -w 8 -V 0 -E 747118613 -d -k -J -O 0 -L 16 -H $SIGNATURE_GUIDE_MODE -p"
export SCORR_ARGS='-F 1 -C 1000'
export ABC_CEX_MODE=2 ABC_CEX_COMPRESS=4 ABC_CEX_PACK_FAST=2
export ABC_CEX_PROJECT_ALL=0
exec bash "$SCRIPT_DIR/run_bench_parallel.sh" "$@"
