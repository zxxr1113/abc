#!/usr/bin/env bash
# Run the first phase=SEQ Build profiling sweep with 2-3 configs in parallel.
# Example for a 64-core server:
#   MAX_PARALLEL=3 JOBS_PER_RUN=20 ./scripts/run_bench_parallel.sh
# Keep MAX_PARALLEL * JOBS_PER_RUN within the server CPU budget.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCH_SCRIPT="$SCRIPT_DIR/bench_scorr_then_stran.py"
ANALYZE_SCRIPT="$SCRIPT_DIR/analyze_stran_build_sweep.py"

# ---- fixed settings ----
AIG_DIR="${AIG_DIR:-$HOME/benchmark/all_test/all/bitlevel}"
#AIG_DIR="${AIG_DIR:-$HOME/benchmark/stran_quick_test}"
ABC="${ABC:-$HOME/abc/abc}"
TIMEOUT="${TIMEOUT:-7200}"
LIMIT="${LIMIT:-}"
OUT_DIR="${OUT_DIR:-seqbuild_schema7_$(date -u +%Y%m%dT%H%M%SZ)}"
MAX_PARALLEL="${MAX_PARALLEL:-3}"
JOBS_PER_RUN="${JOBS_PER_RUN:-20}"
SKIP_DSEC="${SKIP_DSEC:-1}"
# ---- end fixed settings ----

# ---- parameter sweeps (edit here) ----
# Format: "stran_args  tag"
# - stran_args: quoted string passed to --stran-args
# - tag:        short label used in the output CSV filename
#
# The base &scorr pass is shared across all experiments.
# Set SCORR_ARGS below to control it.

SCORR_ARGS="${SCORR_ARGS:--F 1 -C 100}"

# Historical sweep retained for reference only; main() does not run it.
LEGACY_EXPERIMENTS=(
    # "stran_args"                                  "tag"

    # "-d -C 100 -P root -p -V 0 -N 10 -B 32 -z"  "root_C100_V0_N10_B32"
    # "-d -C 100 -P root -p -V 0 -N 10 -B 64 -z -q 8 -w 5"  "root_C100_V0_N10_B64"
    # "-d -C 100 -P root -p -V 0 -N 10 -B 16 -z"  "root_C100_V0_N10_B16"
    # "-d -C 100 -P root -p -V 0 -N 10 -w 2 -z"  "root_C100_V0_N10_w2"
    # "-d -C 100 -P root -p -V 0 -N 10 -w 4 -z"  "root_C100_V0_N10_w4"

    # "-d -C 100 -P root -p -V 0 -N 10 -q 3 -z"  "root_C100_V0_N10_q3" 
    # "-d -C 100 -P root -p -V 0 -N 10 -q 3 -w 2 -z"  "root_C100_V0_N10_q3_w2"
    # "-d -C 100 -P root -p -V 0 -N 10 -q 5 -z"  "root_C100_V0_N10_q5" 
    # "-d -C 100 -P root -p -V 0 -N 10 -q 5 -w 2 -z"  "root_C100_V0_N10_q5_w2"
    # "-d -C 100 -P root -p -V 0 -N 10 -B 64 -q 8 -w 5"  "root_C100_V0_N10_q8_w5" 
    # "-d -C 100 -P root -p -V 0 -N 10 -B 64 -q 8 -w 5 -r"  "root_C100_V0_N10_q8_w5_r"
    # "-d -C 100 -P root -p -V 0 -N 10 -B 64 -q 8 -w 5 -r -z"  "root_C100_V0_N10_q8_w5_r_z"

    # "-d -C 500 -P root -p -V 0 -N 10 -c"  "root_C500_V0_N10_c"
    # "-d -C 200 -P root -p -V 0 -N 10 -r"  "root_C200_V0_N10_r"
    # "-P root -F 1 -C 100 -S -1 -b 100 -N 20 -K 0 -B 0 -L 0 -w 64 -q 8 -r -G 1 -O 0 -m 0 -J 0 -U 0 -Q 16 -W 32 -E 16 -R 128 -H 1 -a 16 -e 128 -p" "root_best_result"

    "-C 100 -b 100 -P root -p -N 10 -B 16 -r -K 8"  "root_C100_V0_N10_B16"
    "-C 100 -b 100 -P root -p -N 10 -B 16 -r -K 8 -q 16"  "root_C100_V0_N10_B16_q16"
    
    "-C 100 -b 100 -P root -p -N 10 -B 32 -r -K 8"  "root_C100_V0_N10_B32"
    "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 8"  "root_C100_V0_N10_B64"

    "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 16"  "root_C100_V0_N10_B64_K16"

    "-C 300 -b 300 -P root -p -N 10 -B 64 -r -K 8"  "root_C300_V0_N10_B64_K8"
    "-C 500 -b 500 -P root -p -N 10 -B 64 -r -K 8"  "root_C500_V0_N10_B64_K8"
    "-C 500 -b 500 -P root -p -N 10 -B 64 -r -K 8 -q 16"  "root_C500_V0_N10_B64_K8_q16"

    



)

# First round used by main().  Each non-reference config changes one Build
# discovery control, so phase=SEQ gain/time differences remain interpretable.
SEQBUILD_EXPERIMENTS=(
    "-P root -F 1 -C 1000 -b 100 -N 10 -B 64 -K 5 -q 30 -j 5 -w 8 -r -p"
    "seqbuild_ref_N10_B64_q30"
    "-P root -F 1 -C 1000 -b 100 -N 10 -B 32 -K 5 -q 30 -j 5 -w 8 -r -p"
    "seqbuild_B32"
    "-P root -F 1 -C 1000 -b 100 -N 10 -B 64 -K 5 -q 15 -j 5 -w 8 -r -p"
    "seqbuild_q15"
)
# ---- end parameter sweeps ----

# ---- helpers ----
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
    [[ -n "$LIMIT" ]] && command+=(--limit "$LIMIT")
    [[ "$SKIP_DSEC" == "1" ]] && command+=(--skip-dsec)

    echo "[launch] tag=$tag out=$csv_out jobs=$JOBS_PER_RUN"
    "${command[@]}" > >(tee "$log_out") 2>&1
    echo "[done] tag=$tag out=$csv_out"
}
# ---- end helpers ----

main() {
    local required
    for required in "$BENCH_SCRIPT" "$SCRIPT_DIR/stran_profile.py" "$ANALYZE_SCRIPT"; do
        if [[ ! -f "$required" ]]; then
            echo "ERROR: required file not found: $required" >&2
            exit 2
        fi
    done
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

    local n=${#SEQBUILD_EXPERIMENTS[@]}
    if [[ $((n % 2)) -ne 0 ]]; then
        echo "ERROR: SEQBUILD_EXPERIMENTS must contain args/tag pairs" >&2
        exit 1
    fi

    local total=$(( n / 2 ))
    echo "==== phase=SEQ Build profiling ===="
    echo "experiments: $total max_parallel: $MAX_PARALLEL jobs_per_run: $JOBS_PER_RUN"
    echo "aig_dir: $AIG_DIR"
    echo "abc:     $ABC"
    echo "timeout: ${TIMEOUT}s"
    echo "scorr:   $SCORR_ARGS"
    echo "out_dir: $OUT_DIR"
    echo "skip_dsec: $SKIP_DSEC"
    echo ""

    local idx=0 failures=0 batch_end pid
    while [[ $idx -lt $total ]]; do
        local pids=()
        batch_end=$((idx + MAX_PARALLEL))
        (( batch_end > total )) && batch_end=$total
        while [[ $idx -lt $batch_end ]]; do
            local args="${SEQBUILD_EXPERIMENTS[$((idx * 2))]}"
            local tag="${SEQBUILD_EXPERIMENTS[$((idx * 2 + 1))]}"
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
        echo "ERROR: $failures config run(s) failed; inspect $OUT_DIR/*.log" >&2
        exit 1
    fi

    local csvs=()
    for ((idx = 0; idx < total; idx++)); do
        csvs+=("$OUT_DIR/stran_${SEQBUILD_EXPERIMENTS[$((idx * 2 + 1))]}.csv")
    done
    python3 "$ANALYZE_SCRIPT" --reference-first "${csvs[@]}" \
        | tee "$OUT_DIR/analysis_seq_build.txt"

    echo ""
    echo "==== all done ===="
    ls -lh "$OUT_DIR"/stran_*.csv "$OUT_DIR/analysis_seq_build.txt"
}

main "$@"
