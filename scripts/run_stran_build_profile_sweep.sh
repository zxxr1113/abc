#!/usr/bin/env bash
# First-stage Build-discovery profiling sweep.  Run this on the compact suite
# produced by collect_seqbuild_cases.sh; configurations are intentionally
# isolated so B/K/N/q effects are interpretable.
set -euo pipefail

: "${AIG_DIR:?set AIG_DIR to the compact local/server suite}"
ABC_BIN="${ABC_BIN:-./abc}"
OUT_DIR="${OUT_DIR:-stran_build_profile_$(date -u +%Y%m%dT%H%M%SZ)}"
JOBS="${JOBS:-1}"
TIMEOUT="${TIMEOUT:-7200}"
SCORR_ARGS="${SCORR_ARGS:--C 100}"
SKIP_DSEC="${SKIP_DSEC:-0}"

mkdir -p "$OUT_DIR"

common=(-P root -F 1 -C 1000 -b 100 -j 5 -w 8 -r -p)
configs=(
  "ref|-N 10 -B 64 -K 5 -q 30"
  "B32|-N 10 -B 32 -K 5 -q 30"
  "B16|-N 10 -B 16 -K 5 -q 30"
  "q15|-N 10 -B 64 -K 5 -q 15"
  "N5|-N 5 -B 64 -K 5 -q 30"
  "K3|-N 10 -B 64 -K 3 -q 30"
  "B32_q15|-N 10 -B 32 -K 5 -q 15"
)

runner=(
  python3 scripts/bench_scorr_then_stran.py
  --aig-dir "$AIG_DIR"
  --abc "$ABC_BIN"
  --jobs "$JOBS"
  --timeout "$TIMEOUT"
  --scorr-args "$SCORR_ARGS"
)
if [[ "$SKIP_DSEC" == "1" ]]; then
  runner+=(--skip-dsec)
fi

for entry in "${configs[@]}"; do
  tag="${entry%%|*}"
  specific="${entry#*|}"
  args="${common[*]} $specific"
  echo "[PROFILE] $tag: $args"
  "${runner[@]}" \
    --stran-args "$args" \
    --out "$OUT_DIR/$tag.csv"
done

echo "[DONE] $OUT_DIR"
