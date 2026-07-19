#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   ABC_BIN=./abc STRAN_ARGS='-F 1 -C 1000 -T 1000 -N 100 -D 32 -B 64 -K 32 -Q 4 -W 8' \
#     bash scripts/run_stran_v2_bench.sh results/stran-v2 benchmark/a.aig benchmark/b.aig
#
# Each result directory contains before/after AIGs and an independent dsec
# audit in run.log.  Use -B 0 only for deliberately small all-pairs runs.

if (( $# < 2 )); then
    echo "usage: $0 <result-dir> <benchmark.aig> [benchmark.aig ...]" >&2
    exit 2
fi

abc_bin=${ABC_BIN:-./abc}
result_dir=$1
shift
stran_args=${STRAN_ARGS:--F 1 -C 1000 -S -1 -T 1000 -N 100 -D 32 -B 64 -K 32 -Q 4 -W 8}
shadow_args=${STRAN_SHADOW:--f}

mkdir -p "$result_dir"
summary="$result_dir/summary.tsv"
printf 'benchmark\tstatus\tfinal-statistics\n' > "$summary"

for benchmark_path in "$@"; do
    if [[ ! -f "$benchmark_path" ]]; then
        echo "missing benchmark: $benchmark_path" >&2
        exit 2
    fi
    benchmark_name=$(basename "$benchmark_path")
    benchmark_name=${benchmark_name%.*}
    run_dir="$result_dir/$benchmark_name"
    mkdir -p "$run_dir"
    before_path="$run_dir/before.aig"
    after_path="$run_dir/after.aig"
    log_path="$run_dir/run.log"

    set +e
    "$abc_bin" -q "r $benchmark_path; write_aiger $before_path; &get; &stran $stran_args $shadow_args; &write $after_path; dsec $before_path $after_path" >"$log_path" 2>&1
    status=$?
    set -e
    final_stat=$(grep 'Sequential transduction:.*proofs=' "$log_path" | tail -1 || true)
    if (( status == 0 )) && grep -q 'Networks are equivalent' "$log_path"; then
        printf '%s\tPASS\t%s\n' "$benchmark_path" "$final_stat" >> "$summary"
    else
        printf '%s\tFAIL(%d)\t%s\n' "$benchmark_path" "$status" "$final_stat" >> "$summary"
    fi
done

column -t -s $'\t' "$summary" 2>/dev/null || cat "$summary"
