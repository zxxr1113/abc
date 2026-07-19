#!/usr/bin/env bash
set -euo pipefail

# Run comparable &stran configurations.  Each configuration is isolated in
# its own directory and inherits the per-run before/after/dsec audit from
# run_stran_v2_bench.sh.
#
# Usage:
#   bash scripts/run_stran_v2_sweep.sh results/stran-sweep benchmark/a.aig
#
# Override STRAN_SWEEP_CONFIGS with newline-delimited "name|arguments" rows.
# Example:
#   STRAN_SWEEP_CONFIGS=$'single|-M 1 -T 200 ...\npair|-M 2 -T 200 ...'

if (( $# < 2 )); then
    echo "usage: $0 <result-dir> <benchmark.aig> [benchmark.aig ...]" >&2
    exit 2
fi

result_dir=$1
shift
abc_bin=${ABC_BIN:-./abc}
shadow_args=-f
if [[ ${STRAN_SHADOW+x} ]]; then
    shadow_args=$STRAN_SHADOW
fi
configs=${STRAN_SWEEP_CONFIGS:-$'single|-M 1 -F 1 -C 1000 -S -1 -T 1000 -N 100 -D 32 -B 64 -K 32 -Q 4 -W 8\npair|-M 2 -F 1 -C 1000 -S -1 -T 1000 -N 100 -D 32 -B 64 -K 32 -Q 4 -W 8'}

mkdir -p "$result_dir"
summary="$result_dir/sweep.tsv"
printf 'configuration\tbenchmark\tstatus\tfinal-statistics\n' > "$summary"

while IFS='|' read -r config_name stran_args; do
    [[ -z "$config_name" ]] && continue
    if [[ -z "$stran_args" ]]; then
        echo "invalid STRAN_SWEEP_CONFIGS row: $config_name" >&2
        exit 2
    fi
    config_dir="$result_dir/$config_name"
    ABC_BIN="$abc_bin" STRAN_ARGS="$stran_args" STRAN_SHADOW="$shadow_args" \
        bash scripts/run_stran_v2_bench.sh "$config_dir" "$@"
    while IFS=$'\t' read -r benchmark status final_stat; do
        [[ "$benchmark" == "benchmark" ]] && continue
        printf '%s\t%s\t%s\t%s\n' "$config_name" "$benchmark" "$status" "$final_stat" >> "$summary"
    done < "$config_dir/summary.tsv"
done <<< "$configs"

column -t -s $'\t' "$summary" 2>/dev/null || cat "$summary"
