#!/usr/bin/env bash
# Fixed-budget TFO / TFO+CEX / TFO+ODC+CEX comparison.
# CEX_ENABLED controls constructor teaching; proof-oracle CEX remain enabled.
# Default: TFO+CEX. ODC_ENABLED=1 adds the existing long-observation/H2 package.
set -euo pipefail
SCRIPT_DIR="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"
ODC_ENABLED="${ODC_ENABLED:-0}"
CEX_ENABLED="${CEX_ENABLED:-1}"
STRICT_CEX_MODE="${STRICT_CEX_MODE:-4}"
STRICT_CEX_SOLVER="${STRICT_CEX_SOLVER:-1}"
SIGNATURE_GUIDE_MODE="${SIGNATURE_GUIDE_MODE:-2}"
for value in "$ODC_ENABLED" "$CEX_ENABLED" "$STRICT_CEX_SOLVER"; do
    case "$value" in 0|1) ;; *) echo 'ERROR: ODC_ENABLED, CEX_ENABLED and STRICT_CEX_SOLVER must be 0 or 1' >&2; exit 1 ;; esac
done
case "$STRICT_CEX_MODE" in
    0|1|2|3|4|5|6) ;;
    *) echo 'ERROR: STRICT_CEX_MODE must be 0..6' >&2; exit 1 ;;
esac
case "$SIGNATURE_GUIDE_MODE" in
    0|1|2|3) ;;
    *) echo 'ERROR: SIGNATURE_GUIDE_MODE must be 0..3' >&2; exit 1 ;;
esac
export ABC_STRICT_CEX_INITIAL="$CEX_ENABLED"
export ABC_STRICT_CEX_SOLVER="$STRICT_CEX_SOLVER"
export ABC_STRICT_CEX_MODE=0 ABC_CEX_MODE=0 ABC_CEX_COMPRESS=0
export ABC_CEX_PACK_FAST=2 ABC_CEX_PROJECT_ALL=0
export STRAN_ARGS='-P root -F 1 -C 1000 -b 100 -S -1 -N 20 -B 16 -T 8 -D 1 -K 8 -Q 4 -W 8 -q 20 -j 5 -w 8 -V 0 -E 747118613 -d -p'
export SCORR_ARGS='-F 1 -C 1000'
if [[ "$CEX_ENABLED" == 1 ]]; then
    export ABC_STRICT_CEX_MODE="$STRICT_CEX_MODE"
fi
if [[ "$ODC_ENABLED" == 1 ]]; then
    STRAN_ARGS+=' -k -J -O 0 -L 16'
    if [[ "$CEX_ENABLED" == 1 ]]; then
        export ABC_CEX_MODE=2 ABC_CEX_COMPRESS=4
        STRAN_ARGS+=" -H $SIGNATURE_GUIDE_MODE"
    fi
fi
printf 'Constructor teaching: initial=%s strict-mode=%s solver=%s ODC=%s ODC-observation-mode=%s\n' \
    "$ABC_STRICT_CEX_INITIAL" "$ABC_STRICT_CEX_MODE" "$ABC_STRICT_CEX_SOLVER" "$ODC_ENABLED" "$ABC_CEX_MODE"
exec bash "$SCRIPT_DIR/run_bench_parallel.sh" "$@"
