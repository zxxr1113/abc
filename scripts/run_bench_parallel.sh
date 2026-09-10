#!/usr/bin/env bash
# Run the current paired matrix; raw CSVs go to the invoking directory.
set -euo pipefail

SCRIPT_DIR="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"
AIG_DIR="${AIG_DIR:-$HOME/benchmark/stran_seq_build_quick_v7/non_timeout_20260904/bitlevel}"
ABC="${ABC:-$HOME/abc/abc}"
TIMEOUT="${TIMEOUT:-1800}"
LIMIT="${LIMIT:-}"
MAX_PARALLEL="${MAX_PARALLEL:-2}"
JOBS_PER_EXPERIMENT="${JOBS_PER_EXPERIMENT:-32}"
SCORR_ARGS="${SCORR_ARGS-}"
STRAN_ARGS="${STRAN_ARGS:--Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -E 5 -p}"
SKIP_DSEC="${SKIP_DSEC:-1}"
KEEP_ARTIFACTS="${KEEP_ARTIFACTS:-0}"
DRY_RUN="${DRY_RUN:-0}"

EXPERIMENT_FLOWS=(scorr-stran stran2)
EXPERIMENT_TAGS=(current_stran current_stran2)

if [[ -n "${EXPERIMENT_SET:-}" && "$EXPERIMENT_SET" != current ]]; then
    echo "ERROR: historical EXPERIMENT_SET was archived; current matrix has two flows" >&2
    exit 1
fi
if [[ -n "$LIMIT" && ! "$LIMIT" =~ ^[1-9][0-9]*$ ]]; then
    echo "ERROR: LIMIT must be a positive integer" >&2
    exit 1
fi
if [[ "$DRY_RUN" != 0 && "$DRY_RUN" != 1 ]]; then
    echo "ERROR: DRY_RUN must be 0 or 1" >&2
    exit 1
fi
for value in "$MAX_PARALLEL" "$JOBS_PER_EXPERIMENT" "$TIMEOUT"; do
    if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
        echo "ERROR: parallelism, jobs and timeout must be positive integers" >&2
        exit 1
    fi
done
if (( MAX_PARALLEL > 200 || JOBS_PER_EXPERIMENT > 200 || MAX_PARALLEL * JOBS_PER_EXPERIMENT > 200 )); then
    echo "ERROR: worker budget exceeds 200" >&2
    exit 1
fi
if [[ "$SKIP_DSEC" != 0 && "$SKIP_DSEC" != 1 ]]; then
    echo "ERROR: SKIP_DSEC must be 0 or 1" >&2
    exit 1
fi
if [[ "$KEEP_ARTIFACTS" != 0 && "$KEEP_ARTIFACTS" != 1 ]]; then
    echo "ERROR: KEEP_ARTIFACTS must be 0 or 1" >&2
    exit 1
fi
if [[ ! -x "$ABC" || ! -d "$AIG_DIR" ]]; then
    echo "ERROR: ABC executable or AIG_DIR is missing" >&2
    exit 1
fi
for tag in "${EXPERIMENT_TAGS[@]}"; do
    if [[ -e "stran_${tag}.csv" || -e "stran_${tag}.csv.tmp" ]]; then
        echo "ERROR: refusing to overwrite stran_${tag}.csv" >&2
        exit 1
    fi
done

run_one() {
    local flow="$1" tag="$2"
    local command=(python3 "$SCRIPT_DIR/bench_scorr_then_stran.py"
        --aig-dir "$AIG_DIR" --abc "$ABC" --timeout "$TIMEOUT"
        --out "stran_${tag}.csv" --jobs "$JOBS_PER_EXPERIMENT"
        --scorr-args "$SCORR_ARGS" --stran-args "$STRAN_ARGS" --flow "$flow")
    [[ -z "$LIMIT" ]] || command+=(--limit "$LIMIT")
    [[ "$SKIP_DSEC" == 0 ]] || command+=(--skip-dsec)
    [[ "$KEEP_ARTIFACTS" == 0 ]] || command+=(--keep-artifacts)
    printf '[launch] '
    printf '%q ' "${command[@]}"
    printf '\n'
    [[ "$DRY_RUN" == 1 ]] || "${command[@]}"
}

printf 'Workers: at most %s x %s; TMPDIR=%s\n' "$MAX_PARALLEL" "$JOBS_PER_EXPERIMENT" "${TMPDIR:-/tmp}"
pids=()
failed=0
for idx in "${!EXPERIMENT_FLOWS[@]}"; do
    run_one "${EXPERIMENT_FLOWS[$idx]}" "${EXPERIMENT_TAGS[$idx]}" &
    pids+=("$!")
    if (( ${#pids[@]} == MAX_PARALLEL )); then
        for pid in "${pids[@]}"; do
            wait "$pid" || failed=1
        done
        pids=()
    fi
done
for pid in "${pids[@]}"; do
    wait "$pid" || failed=1
done
exit "$failed"
