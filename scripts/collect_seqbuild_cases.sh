#!/bin/bash
# Build a compact local &stran suite with both Build-positive cases and
# expensive zero-Build controls.  Source paths are recorded in manifest.tsv.
#
# Usage: bash collect_seqbuild_cases.sh BENCH_ROOT OUTPUT_DIR [core|all]
set -euo pipefail

BENCH="${1:?benchmark root is required}"
TARGET="${2:?output directory is required}"
PROFILE="${3:-core}"

if [[ ! -d "$BENCH" ]]; then
  echo "ERROR: benchmark root not found: $BENCH" >&2
  exit 2
fi
if [[ "$PROFILE" != "core" && "$PROFILE" != "all" ]]; then
  echo "ERROR: profile must be core or all" >&2
  exit 2
fi

mkdir -p "$TARGET"
TMP=$(mktemp)
trap 'rm -f "$TMP"' EXIT

core_names=(
  loopv3.aig
  vis_QF_BV_bcuvis32.aig
  Float_div.i.p+cfa-reducer.aig
  cal135.aig
  cal157.aig
  cal188.aig
  xepic_a12.aig
  circular_pointer_top_w64_d16_e0.aig
  arbitrated_top_n3_w8_d32_e0.aig
  minepump_spec3_product38.cil.aig
)
extra_names=(
  cal191.aig cal206.aig cal211.aig counter_bit_width_small.aig
  microban_145.aig microban_148.aig microban_33.aig microban_64.aig
  microban_77.aig microban_89.aig vis_arrays_am2910_p3.aig
  circular_pointer_top_w128_d32_e0.aig
  arbitrated_top_n3_w8_d128_e0.aig
  shift_register_top_w128_d16_e0.aig
  pc_sfifo_2.cil-2+token_ring.09.cil-1.aig
)
names=("${core_names[@]}")
if [[ "$PROFILE" == "all" ]]; then
  names+=("${extra_names[@]}")
fi

find "$BENCH" -type f -name '*.aig' | awk -F/ '
  NR==FNR { want[$1]=1; next }
  { b=$NF; if (b in want) print b "\t" $0 }
' <(printf '%s\n' "${names[@]}") - > "$TMP"

while IFS=$'\t' read -r b src; do
  dst="$TARGET/$b"; i=1
  while [ -e "$dst" ]; do dst="$TARGET/${b%.aig}_$i.aig"; i=$((i+1)); done
  cp "$src" "$dst"
done < "$TMP"

{
  printf 'basename\tsource\n'
  sort "$TMP"
} > "$TARGET/manifest.tsv"

echo "copied $(wc -l < "$TMP" | tr -d ' ') files to $TARGET ($PROFILE suite)"
awk 'NR==FNR{m[$1]=1;next} !($1 in m){print "MISSING: "$1}' "$TMP" <(printf '%s\n' "${names[@]}")
