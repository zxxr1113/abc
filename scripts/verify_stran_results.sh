#!/usr/bin/env bash
# Verify outputs of run_stran_bench.sh against their source benchmarks.
# Usage: scripts/verify_stran_results.sh <input-dir> <output-dir> [ABC binary]
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
    echo "usage: $0 <input-dir> <output-dir> [ABC binary]" >&2
    exit 2
fi

input_dir=$1
output_dir=$2
abc_bin=${3:-./abc}
status=0

while IFS= read -r -d '' input; do
    base=$(basename "$input")
    output="$output_dir/${base%.aig}.stran.aig"
    if [[ ! -f "$output" ]]; then
        echo "[missing] $output" >&2
        status=1
        continue
    fi
    echo "[dsec] $base"
    "$abc_bin" -q "dsec $input $output" || status=1
done < <(find "$input_dir" -type f -name '*.aig' -print0)

exit "$status"
