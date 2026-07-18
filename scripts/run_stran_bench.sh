#!/usr/bin/env bash
# Run bounded &stran over a directory of sequential AIGER benchmarks.
# Usage: scripts/run_stran_bench.sh <input-dir> <output-dir> [ABC binary]
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
    echo "usage: $0 <input-dir> <output-dir> [ABC binary]" >&2
    exit 2
fi

input_dir=$1
output_dir=$2
abc_bin=${3:-./abc}
stran_args=${STRAN_ARGS:--F 1 -C 1000 -S -1 -T 1000 -N 100 -D 16}

mkdir -p "$output_dir"
while IFS= read -r -d '' input; do
    base=$(basename "$input")
    stem=${base%.aig}
    output="$output_dir/${stem}.stran.aig"
    log="$output_dir/${stem}.stran.log"
    echo "[&stran] $input"
    "$abc_bin" -q "&r $input; &stran $stran_args; &ps; &write $output" >"$log" 2>&1 || {
        echo "[&stran] failed: $input (see $log)" >&2
        continue
    }
done < <(find "$input_dir" -type f -name '*.aig' -print0)
