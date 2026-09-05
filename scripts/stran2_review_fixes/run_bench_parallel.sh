#!/usr/bin/env bash
# Run bench_scorr_then_stran.py with multiple parameter configs in parallel.
# Usage: ./scripts/run_bench_parallel.sh
#
# Edit the arrays below to control which experiments run.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCH_SCRIPT="$SCRIPT_DIR/bench_scorr_then_stran.py"

# ---- fixed settings ----
AIG_DIR="${AIG_DIR:-$HOME/benchmark/all_test/all/bitlevel}"
#AIG_DIR="${AIG_DIR:-$HOME/benchmark/stran_quick_test}"
ABC="${ABC:-$HOME/abc/abc}"
TIMEOUT="${TIMEOUT:-1800}"
LIMIT="${LIMIT:-}"
# Max concurrent experiment groups (each group spawns its own --jobs workers).
MAX_PARALLEL="${MAX_PARALLEL:-4}"
JOBS_PER_EXPERIMENT="${JOBS_PER_EXPERIMENT:-50}"
EXPERIMENT_SET="${EXPERIMENT_SET:-review_fixes}"
# Multi-path needs a wider candidate horizon to expose its potential.  Keep
# q=20 as the normal batch default; override only for an explicit q sweep.
MULTIPATH_Q="${MULTIPATH_Q:-20}"
# ---- end fixed settings ----

# ---- parameter sweeps (edit here) ----
# Format: "stran_args  tag"
# - stran_args: quoted string passed to --stran-args
# - tag:        short label used in the output CSV filename
#
# The base &scorr pass is shared across all experiments.
# Set SCORR_ARGS below to control it.

SCORR_ARGS="${SCORR_ARGS--C 100}"

# Add your experiments here.  Each line spawns one CSV.
EXPERIMENTS=(
    # "stran_args"                                  "tag"

    # "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 8 "  "root_C100_V0_N10_B64"
    # "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 8 -w 10"  "root_C100_V0_N10_B64_w10"


    # "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 8 -q 20 -w 10"  "root_C100_V0_N10_B64_q20_w10"
    # "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 8 -q 20 -w 10 -y"  "root_C100_V0_N10_B64_q20_w10_y"
    # "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 8 -q 20 -w 10 -M"  "root_C100_V0_N10_B64_q20_w10_M" 

    # "-C 1000 -b 1000 -P root -p -N 10 -B 64 -r -K 8 -q 20 -w 10"  "root_C1000_V0_N10_B64_q20_w10"
    # "-C 0 -b 100 -P root -p -N 20 -B 128 -K 16 -q 4 -w 0"  "root_C0_V0_N20_B128_K16_q16_w0"

    # "-C 100 -b 100 -P root -p -N 10 -B 64 -K 5 -q 4 -w 8"  "root_C100_V0_N10_B64_K5_q4_w8_v2"
    # "-C 100 -b 100 -P root -p -N 10 -B 64 -K 5 -q 4 -w 8 -u"  "root_C100_V0_N10_B64_K5_q4_w8_u_v2"

    # "-C 100 -b 100 -P root -p -N 10 -B 64 -K 10 -q 10 -w 8"  "root_C100_V0_N10_B64_K10_q10_w8_v2"
    # "-C 100 -b 100 -P root -p -N 10 -B 64 -K 10 -q 10 -w 8 -u"  "root_C100_V0_N10_B64_K10_q10_w8_u_v2"


    "-C 1000 -b 100 -P root -p -N 10 -B 32 -K 5 -q 15 -j 5 -w 3"  "root_C1000_N10_B32_K5_q15_j5_w3_v7"
    "-C 1000 -b 100 -P root -p -N 20 -B 64 -K 10 -q 5 -j 5 -w 8"  "root_C1000_N20_B64_K10_q5_j5_w8_v7"
    "-C 1000 -b 100 -P root -p -N 20 -B 64 -K 10 -q 10 -j 5 -w 8"  "root_C1000_N20_B64_K10_q10_j5_w8_v7"

    "-C 1000 -b 100 -P root -p -N 20 -B 32 -K 10 -q 15 -j 5 -w 8"  "root_C1000_N20_B32_K10_q15_j5_w8_v7"
    "-C 1000 -b 100 -P root -p -N 20 -B 64 -K 10 -q 15 -j 5 -w 8"  "root_C1000_N20_B64_K10_q15_j5_w8_v7"
    "-C 1000 -b 100 -P root -p -N 20 -B 64 -K 10 -q 15 -j 5 -w 4"  "root_C1000_N20_B64_K10_q15_j5_w4_v7"
    "-C 1000 -b 100 -P root -p -N 10 -B 32 -K 10 -q 15 -j 5 -w 4"  "root_C1000_N20_B32_K10_q15_j5_w4_v7"

    # "-C 1000 -b 100 -P root -p -N 20 -B 64 -K 10 -q 15 -j 5 -w 8 -Q 2 -W 4"  "root_C1000_N20_B64_K10_q15_j5_w8_Q2_W4_v5"
     
    

    # "-C 0 -b 100 -P root -p -N 10 -B 64 -K 5 -q 8 -w 0 -u"  "root_C0_V0_N10_B64_K5_q8_w0_u"
    # "-C 0 -b 100 -P root -p -N 10 -B 64 -K 5 -q 8 -w 0 -M"  "root_C0_V0_N10_B64_K5_q8_w0_M"


    #"-C 100 -b 100 -P root -p -N 10 -B 64 -K 5 -q 8 -w 0"  "root_C100_V0_N10_B64_K5_q8_w0"


    # "-C 0 -b 100 -P root -p -N 10 -B 64 -K 5 -q 4 -w 8 -u"  "root_C0_V0_N10_B64_K5_q4_w8_u_v2"

    #"-C 0 -b 100 -P root -p -N 20 -B 128 -K 16 -q 1 -w 0"  "root_C0_V0_N20_B128_K16_q4_w0_v3"

    # "-C 0 -b 100 -P root -p -N 20 -B 128 -K 16 -q 0 -w 0 -M"  "root_C0_V0_N20_B128_K16_q0_w0_m_v3"
    # "-C 0 -b 100 -P root -p -N 20 -B 128 -K 16 -q 0 -w 0 -y"  "root_C0_V0_N20_B128_K16_q0_w0_y_v3"


    # "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 8 -w 10"  "root_C100_V0_N10_B64_w10"

    # "-C 100 -b 100 -P root -p -N 10 -B 64 -r -K 16"  "root_C100_V0_N10_B64_K16"

    # "-C 300 -b 300 -P root -p -N 10 -B 64 -r -K 8 "  "root_C300_V0_N10_B64_K8"
    # "-C 500 -b 500 -P root -p -N 10 -B 64 -r -K 8 -w 5"  "root_C500_V0_N10_B64_K8_w5"
    # "-C 500 -b 500 -P root -p -N 10 -B 64 -r -K 8 -w 5 -t"  "root_C500_V0_N10_B64_K8_w5_t"

    # "-C 500 -b 500 -P root -p -N 10 -B 64 -r -K 16 -q 20 -t"  "root_C500_V0_N10_B64_K16_q20_t" 

    # "-C 1000 -b 1000 -P root -p -N 20 -B 128 -r -K 16 -q 10 -t -w 30"  "root_C1000_V0_N20_B128_K16_q10_t_w30" 

    # "-C 1000 -b 1000 -P root -p -N 20 -B 128 -r -K 16 -q 0 -w 20"  "root_C1000_V0_N20_B128_K16_q0_w20" 



)
EXPERIMENT_FLOWS=()

if [[ "$EXPERIMENT_SET" == "explore" ]]; then
    EXPERIMENTS=()
    EXPERIMENT_FLOWS=()
    for explore_mode in ${EXPLORE_MODES:-0 1 3 5}; do
        EXPERIMENTS+=("-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -p -E $explore_mode" "explore_E${explore_mode}_Q4_W8_q10")
        EXPERIMENT_FLOWS+=("stran2")
    done
elif [[ "$EXPERIMENT_SET" == "review_fixes" ]]; then
    : "${ABC_BEFORE:?Set ABC_BEFORE to the closure-instrumented pre-fix binary}"
    EXPERIMENTS=(
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -E 5 -p" "before_stran_E5_Q4_W8_q10"
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -E 5 -p" "before_stran2_E5_Q4_W8_q10"
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -E 5 -p" "fixed_stran_E5_Q4_W8_q10"
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -E 5 -p" "fixed_stran2_E5_Q4_W8_q10"
    )
    EXPERIMENT_FLOWS=("scorr-stran" "stran2" "scorr-stran" "stran2")
elif [[ "$EXPERIMENT_SET" == "multipath_v124" ]]; then
    EXPERIMENTS=(
        "-C 1000 -b 100 -P root -p -N 20 -B 64 -K 10 -q $MULTIPATH_Q -j 5 -w 8 -V 1"  "multipath_V1_N20_B64_K10_q${MULTIPATH_Q}_j5_w8"
        "-C 1000 -b 100 -P root -p -N 20 -B 64 -K 10 -q $MULTIPATH_Q -j 5 -w 8 -V 2"  "multipath_V2_N20_B64_K10_q${MULTIPATH_Q}_j5_w8"
        "-C 1000 -b 100 -P root -p -N 20 -B 64 -K 10 -q $MULTIPATH_Q -j 5 -w 8 -V 4"  "multipath_V4_N20_B64_K10_q${MULTIPATH_Q}_j5_w8"
    )
elif [[ "$EXPERIMENT_SET" == "stran2_compare_q48" ]]; then
    EXPERIMENTS=(
        "-Q 4 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "baseline_Q4_q15_j5_w8_C1000_b100"
        "-Q 8 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "baseline_Q8_q15_j5_w8_C1000_b100"
        "-Q 4 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "stran2_Q4_q15_j5_w8_C1000_b100"
        "-Q 8 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "stran2_Q8_q15_j5_w8_C1000_b100"
    )
    EXPERIMENT_FLOWS=("scorr-stran" "scorr-stran" "stran2" "stran2")
elif [[ "$EXPERIMENT_SET" == "stran2_trace_pilot" ]]; then
    EXPERIMENTS=(
        "-Q 4 -W 8 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "baseline_Q4_W8_q15_j5_w8"
        "-Q 4 -W 8 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "stran2_Q4_W8_q15_j5_w8"
        "-Q 2 -W 8 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "stran2_Q2_W8_q15_j5_w8"
        "-Q 1 -W 8 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "stran2_Q1_W8_q15_j5_w8"
    )
    EXPERIMENT_FLOWS=("scorr-stran" "stran2" "stran2" "stran2")
elif [[ "$EXPERIMENT_SET" == "stran2_trace_pilot_tune" ]]; then
    EXPERIMENTS=(
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "stran2_Q4_W8_q10_j5_w8"
        "-Q 4 -W 8 -q 15 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"  "stran2_Q4_W8_q15_j5_w4"
        "-Q 2 -W 8 -q 20 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "stran2_Q2_W8_q20_j5_w8"
        "-Q 2 -W 4 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "stran2_Q2_W4_q15_j5_w8"
    )
    EXPERIMENT_FLOWS=("stran2" "stran2" "stran2" "stran2")
elif [[ "$EXPERIMENT_SET" == "stran2_trace_full" ]]; then
    EXPERIMENTS=(
        "-Q 4 -W 8 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "full_baseline_Q4_W8_q15_j5_w8"
        "-Q 4 -W 8 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "full_stran2_Q4_W8_q15_j5_w8"
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "full_stran2_Q4_W8_q10_j5_w8"
        "-Q 2 -W 4 -q 15 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "full_stran2_Q2_W4_q15_j5_w8"
    )
    EXPERIMENT_FLOWS=("scorr-stran" "stran2" "stran2" "stran2")
elif [[ "$EXPERIMENT_SET" == "stran2_budget_pilot" ]]; then
    # Strict same-parameter pairs for measuring q/w budget reduction and the
    # large-signature/small-q hypothesis on the 32-case quick suite.
    EXPERIMENTS=(
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "budget_pilot_baseline_Q4_W8_q10_j5_w8"
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "budget_pilot_stran2_Q4_W8_q10_j5_w8"
        "-Q 4 -W 8 -q 8 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"   "budget_pilot_baseline_Q4_W8_q8_j5_w4"
        "-Q 4 -W 8 -q 8 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"   "budget_pilot_stran2_Q4_W8_q8_j5_w4"
        "-Q 4 -W 8 -q 5 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"   "budget_pilot_baseline_Q4_W8_q5_j5_w4"
        "-Q 4 -W 8 -q 5 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"   "budget_pilot_stran2_Q4_W8_q5_j5_w4"
        "-Q 8 -W 16 -q 5 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"  "budget_pilot_baseline_Q8_W16_q5_j5_w4"
        "-Q 8 -W 16 -q 5 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"  "budget_pilot_stran2_Q8_W16_q5_j5_w4"
        "-Q 8 -W 16 -q 8 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"  "budget_pilot_baseline_Q8_W16_q8_j5_w4"
        "-Q 8 -W 16 -q 8 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"  "budget_pilot_stran2_Q8_W16_q8_j5_w4"
    )
    EXPERIMENT_FLOWS=(
        "scorr-stran" "stran2" "scorr-stran" "stran2"
        "scorr-stran" "stran2" "scorr-stran" "stran2"
        "scorr-stran" "stran2"
    )
elif [[ "$EXPERIMENT_SET" == "stran2_budget_full" ]]; then
    # Full historical-all-PASS follow-up selected by stran2_budget_pilot.
    # Each point is a strict same-parameter baseline/&stran2 pair.
    EXPERIMENTS=(
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "budget_full_baseline_Q4_W8_q10_j5_w8"
        "-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -p"  "budget_full_stran2_Q4_W8_q10_j5_w8"
        "-Q 4 -W 8 -q 5 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"   "budget_full_baseline_Q4_W8_q5_j5_w4"
        "-Q 4 -W 8 -q 5 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"   "budget_full_stran2_Q4_W8_q5_j5_w4"
        "-Q 8 -W 16 -q 5 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"  "budget_full_baseline_Q8_W16_q5_j5_w4"
        "-Q 8 -W 16 -q 5 -j 5 -w 4 -C 1000 -b 100 -V 0 -p"  "budget_full_stran2_Q8_W16_q5_j5_w4"
    )
    EXPERIMENT_FLOWS=(
        "scorr-stran" "stran2" "scorr-stran" "stran2"
        "scorr-stran" "stran2"
    )
elif [[ "$EXPERIMENT_SET" != "default" ]]; then
    echo "ERROR: unknown EXPERIMENT_SET=$EXPERIMENT_SET" >&2
    exit 1
fi
# ---- end parameter sweeps ----

# ---- helpers ----
run_one() {
    local flow="$1"
    local stran_args="$2"
    local tag="$3"
    local csv_out="stran_${tag}.csv"
    local abc="$ABC"
    if [[ "$EXPERIMENT_SET" == "review_fixes" && "$tag" == before_* ]]; then
        abc="$ABC_BEFORE"
    fi

    local extra_args=()
    [[ -n "$LIMIT" ]] && extra_args+=(--limit "$LIMIT")

    echo "[launch] flow=$flow  tag=$tag  out=$csv_out  stran=$stran_args"
    python3 "$BENCH_SCRIPT" \
        --aig-dir "$AIG_DIR" \
        --abc "$abc" \
        --timeout "$TIMEOUT" \
        --out "$csv_out" \
        --jobs "$JOBS_PER_EXPERIMENT" \
        --scorr-args "$SCORR_ARGS" \
        --stran-args "$stran_args" \
        --flow "$flow" \
        --skip-dsec \
        "${extra_args[@]}"
    echo "[done]   flow=$flow  tag=$tag  out=$csv_out"
}
# ---- end helpers ----

main() {
    if (( MAX_PARALLEL * JOBS_PER_EXPERIMENT > 200 )); then
        echo "ERROR: worker budget exceeds 200" >&2
        exit 1
    fi
    if [[ ! -f "$BENCH_SCRIPT" ]]; then
        echo "ERROR: bench_scorr_then_stran.py not found at $BENCH_SCRIPT" >&2
        exit 1
    fi

    # bench_scorr_then_stran.py imports stran_profile; it must sit in the
    # same directory (or be reachable via PYTHONPATH).
    if [[ ! -f "$SCRIPT_DIR/stran_profile.py" ]]; then
        echo "ERROR: stran_profile.py not found next to $BENCH_SCRIPT" >&2
        echo "       Copy stran_profile.py into $SCRIPT_DIR/ and rerun." >&2
        exit 1
    fi
    export PYTHONPATH="$SCRIPT_DIR${PYTHONPATH:+:$PYTHONPATH}"

    local n=${#EXPERIMENTS[@]}
    if [[ $((n % 2)) -ne 0 ]]; then
        echo "ERROR: EXPERIMENTS array must have even length (pairs of args + tag)" >&2
        exit 1
    fi

    local total=$(( n / 2 ))
    if [[ ${#EXPERIMENT_FLOWS[@]} -eq 0 ]]; then
        local flow_idx
        for ((flow_idx = 0; flow_idx < total; flow_idx++)); do
            EXPERIMENT_FLOWS+=("scorr-stran")
        done
    elif [[ ${#EXPERIMENT_FLOWS[@]} -ne $total ]]; then
        echo "ERROR: EXPERIMENT_FLOWS must have one entry per experiment" >&2
        exit 1
    fi
    echo "==== bench_parallel ===="
    echo "experiments: $total   max_parallel: $MAX_PARALLEL"
    echo "jobs/experiment: $JOBS_PER_EXPERIMENT"
    echo "aig_dir: $AIG_DIR"
    echo "abc:     $ABC"
    echo "timeout: ${TIMEOUT}s"
    echo "scorr:   $SCORR_ARGS"
    echo ""

    local running=0
    local idx=0
    while [[ $idx -lt $total ]]; do
        local args="${EXPERIMENTS[$((idx * 2))]}"
        local tag="${EXPERIMENTS[$((idx * 2 + 1))]}"
        local flow="${EXPERIMENT_FLOWS[$idx]}"

        # Wait if we're at the concurrency limit.
        while [[ $running -ge $MAX_PARALLEL ]]; do
            wait -n 2>/dev/null || true
            running=$((running - 1))
        done

        run_one "$flow" "$args" "$tag" &
        running=$((running + 1))
        idx=$((idx + 1))
    done

    # Wait for remaining jobs.
    while [[ $running -gt 0 ]]; do
        wait -n 2>/dev/null || true
        running=$((running - 1))
    done

    echo ""
    echo "==== all done ===="
    ls -lh stran_*.csv 2>/dev/null || true
}

main "$@"
