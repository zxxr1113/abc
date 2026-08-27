#!/usr/bin/env bash
# Run three phase=SEQ Build configurations over the full benchmark directory.
#
# Example for a 64-core server:
#   AIG_DIR=/path/to/all/aigs ABC=/path/to/abc \
#   MAX_PARALLEL=3 JOBS_PER_RUN=20 ./scripts/run_bench_parallel.sh
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCH_SCRIPT="$SCRIPT_DIR/bench_scorr_then_stran.py"

AIG_DIR="${AIG_DIR:-$HOME/benchmark/all_test/all/bitlevel}"
ABC="${ABC:-$HOME/abc/abc}"
OUT_DIR="${OUT_DIR:-seqbuild_full_$(date -u +%Y%m%dT%H%M%SZ)}"
TIMEOUT="${TIMEOUT:-12800}"
MAX_PARALLEL="${MAX_PARALLEL:-3}"
JOBS_PER_RUN="${JOBS_PER_RUN:-20}"
SKIP_DSEC="${SKIP_DSEC:-1}"
SCORR_ARGS="${SCORR_ARGS:--F 1 -C 100}"

# Reference plus two one-variable discovery reductions.
EXPERIMENTS=(
    "-P root -F 1 -C 1000 -b 100 -N 10 -B 64 -K 5 -q 30 -j 5 -w 8 -r -p"
    "seqbuild_ref_N10_B64_q30"
    "-P root -F 1 -C 1000 -b 100 -N 10 -B 32 -K 5 -q 30 -j 5 -w 8 -r -p"
    "seqbuild_B32"
    "-P root -F 1 -C 1000 -b 100 -N 10 -B 64 -K 5 -q 15 -j 5 -w 8 -r -p"
    "seqbuild_q15"
)

run_one() {
    local stran_args="$1"
    local tag="$2"
    local csv_out="$OUT_DIR/stran_${tag}.csv"
    local log_out="$OUT_DIR/stran_${tag}.log"
    local command=(
        python3 "$BENCH_SCRIPT"
        --aig-dir "$AIG_DIR"
        --abc "$ABC"
        --timeout "$TIMEOUT"
        --out "$csv_out"
        --jobs "$JOBS_PER_RUN"
        --scorr-args "$SCORR_ARGS"
        --stran-args "$stran_args"
    )
    [[ "$SKIP_DSEC" == "1" ]] && command+=(--skip-dsec)

    echo "[launch] $tag -> $csv_out"
    "${command[@]}" > >(tee "$log_out") 2>&1
    echo "[done] $tag"
}

main() {
    if [[ ! -f "$BENCH_SCRIPT" || ! -f "$SCRIPT_DIR/stran_profile.py" ]]; then
        echo "ERROR: benchmark runner or profile parser is missing" >&2
        exit 2
    fi
    if [[ ! -d "$AIG_DIR" || ! -x "$ABC" ]]; then
        echo "ERROR: invalid AIG_DIR or ABC: $AIG_DIR / $ABC" >&2
        exit 2
    fi
    if (( MAX_PARALLEL < 1 || MAX_PARALLEL > 3 || JOBS_PER_RUN < 1 )); then
        echo "ERROR: MAX_PARALLEL must be 1..3 and JOBS_PER_RUN must be positive" >&2
        exit 2
    fi
    if [[ "$SKIP_DSEC" != "0" && "$SKIP_DSEC" != "1" ]]; then
        echo "ERROR: SKIP_DSEC must be 0 or 1" >&2
        exit 2
    fi

    mkdir -p "$OUT_DIR"
    export PYTHONPATH="$SCRIPT_DIR${PYTHONPATH:+:$PYTHONPATH}"

    local total=$(( ${#EXPERIMENTS[@]} / 2 ))
    local idx=0 failures=0 batch_end pid

    echo "==== phase=SEQ Build full sweep ===="
    echo "configs=$total max_parallel=$MAX_PARALLEL jobs_per_run=$JOBS_PER_RUN"
    echo "aig_dir=$AIG_DIR"
    echo "abc=$ABC"
    echo "out_dir=$OUT_DIR"
    echo "timeout=${TIMEOUT}s skip_dsec=$SKIP_DSEC"

    while (( idx < total )); do
        local pids=()
        batch_end=$((idx + MAX_PARALLEL))
        (( batch_end > total )) && batch_end=$total
        while (( idx < batch_end )); do
            local args="${EXPERIMENTS[$((idx * 2))]}"
            local tag="${EXPERIMENTS[$((idx * 2 + 1))]}"
            run_one "$args" "$tag" &
            pids+=("$!")
            idx=$((idx + 1))
        done
        for pid in "${pids[@]}"; do
            if ! wait "$pid"; then
                failures=$((failures + 1))
            fi
        done
    done

    if (( failures > 0 )); then
        echo "ERROR: $failures configuration(s) failed; inspect $OUT_DIR/*.log" >&2
        exit 1
    fi

    echo "==== all done ===="
    ls -lh "$OUT_DIR"/stran_*.csv
}

main "$@"
