#!/usr/bin/env bash
set -euo pipefail

abc_bin="${ABC_BIN:-./abc}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

resub_selftest=$("$abc_bin" -q '&stran_resub_test')
printf '%s\n' "$resub_selftest"
grep -q 'stran resub iterator/polarity/canonicalization/MFFC self-test: PASS' <<<"$resub_selftest"
grep -q 'stran ranked-reservoir/global-Existing/helper-remap-HO/all-helper-switch/zero-gain/temp-AIG self-test: PASS' <<<"$resub_selftest"

run_case() {
    local name="$1" blif="$2" opts="$3"
    local out="$tmp_dir/$name.log"
    "$abc_bin" -q "read_blif $blif; strash; write_aiger $tmp_dir/$name-before.aig; &get; &stran -P root -p $opts; &write $tmp_dir/$name-after.aig; dsec $tmp_dir/$name-before.aig $tmp_dir/$name-after.aig" >"$out"
    printf '%s\n' "$(cat "$out")"
    grep -q 'stran-root effect matrix:' "$out"
    grep -q 'stran-root resub iterator:' "$out"
    grep -q 'stran-root dirty:' "$out"
    grep -q 'Networks are equivalent' "$out"
    awk '
        /^  (COMB|SEQ) (CONSTANT|EXISTING|BUILD) / {
            rows++; block_selected += $6; block_marginal += $7
        }
        /stran-root effect totals:/ {
            total_selected = total_marginal = exact = -1
            for (i=1; i<=NF; i++) {
                if ($i ~ /^selected-roots=/) {split($i,a,"="); total_selected=a[2]+0}
                if ($i ~ /^marginal-AND=/) {split($i,a,"="); total_marginal=a[2]+0}
                if ($i ~ /^cleanup-exact-AND=/) {split($i,a,"="); exact=a[2]+0}
            }
            if (rows != 6 || block_selected != total_selected ||
                block_marginal != total_marginal || block_marginal > exact)
                exit 1
            matrices++; rows = block_selected = block_marginal = 0
        }
        /stran-root sequential relations:/ {
            seq_candidates = seeded = helpers = proved = splitn = unknown = -1
            for (i=1; i<=NF; i++) {
                if ($i ~ /^candidates=/) {split($i,a,"="); seq_candidates=a[2]+0}
                if ($i ~ /^seeded=/) {split($i,a,"="); seeded=a[2]+0}
                if ($i ~ /^helper-seeds=/) {split($i,a,"="); helpers=a[2]+0}
                if ($i ~ /^proved=/) {split($i,a,"="); proved=a[2]+0}
                if ($i ~ /^split=/) {split($i,a,"="); splitn=a[2]+0}
                if ($i ~ /^unknown=/) {split($i,a,"="); unknown=a[2]+0}
            }
            if (seq_candidates != proved + splitn + unknown ||
                seeded != seq_candidates + helpers) exit 1
        }
        /stran-root resub iterator:/ {
            initialized = exhausted = page_stops = discarded = invalid = -1
            for (i=1; i<=NF; i++) {
                if ($i ~ /^initialized=/) {split($i,a,"="); initialized=a[2]+0}
                if ($i ~ /^exhausted=/) {split($i,a,"="); exhausted=a[2]+0}
                if ($i ~ /^q-wave-stops=/) {split($i,a,"="); page_stops=a[2]+0}
                if ($i ~ /^snapshot-discarded=/) {split($i,a,"="); discarded=a[2]+0}
                if ($i ~ /^invalid=/) {split($i,a,"="); invalid=a[2]+0}
            }
            # q wave stops are non-terminal.  Every initialized iterator must
            # either exhaust on the immutable snapshot or be discarded when
            # a positive-gain commit invalidates object-indexed state.
            if (initialized != exhausted + discarded ||
                page_stops < 0 || invalid < 0) exit 1
        }
        END {
            if (matrices < 1 || rows != 0) exit 1
        }
    ' "$out"
}

run_case comb test/stran_comb.blif ""
grep -Eq '^  COMB BUILD [0-9]+ [0-9]+ [0-9]+ 1 1 0$' "$tmp_dir/comb.log"
grep -q 'selection=dynamic-max-gain candidates=' "$tmp_dir/comb.log"
grep -Eq 'stran-root commit selection: policy=dynamic-max-gain initial-proved=[1-9][0-9]* initial-positive=[1-9][0-9]* initial-max-gain=([1-9][0-9]*) first-gain=\1 rounds=[1-9][0-9]* gain-evals=[1-9][0-9]*' "$tmp_dir/comb.log"

run_case wave_continue test/stran_helper_remap.blif "-q 1 -S 0 -w 1"
grep -q 'snapshot=immutable scheduler=per-root-q-all-candidates' "$tmp_dir/wave_continue.log"
grep -Eq 'stran-root wave portfolio: waves=[2-9][0-9]* continuations=[1-9][0-9]* .*exhausted=yes' "$tmp_dir/wave_continue.log"
grep -Eq 'stran-root resub iterator: initialized=[1-9][0-9]* .*exhausted=[1-9][0-9]* q-wave-stops=[1-9][0-9]* snapshot-discarded=0' "$tmp_dir/wave_continue.log"

# The helper switch changes only H injection.  Retained proof metadata and
# future dynamic-gain commit eligibility remain present in both modes.
run_case helper_off test/stran_helper_remap.blif "-q 1 -w 2 -u"
grep -q 'stran-root helper batch: enabled=no retained=1 active=0 inactive=1 classes=0 endpoints=0 materialized-gates=0 obligations=3 relation-total=3' "$tmp_dir/helper_off.log"
grep -q 'candidates=3 seeded=3 helper-seeds=0 proved=3 split=0 unknown=0' "$tmp_dir/helper_off.log"
grep -q 'stran-root rounds summary: configured=2 completed=2 comb-passes=1 comb-commits=1 seq-passes=2 seq-commits=1 AND=3->1 gain=2' "$tmp_dir/helper_off.log"

# A physical COMB commit must remap a still-valid zero-gain certificate, rebuild
# the next snapshot, and seed that certificate as H for a later SEQ obligation.
run_case helper_remap test/stran_helper_remap.blif "-q 1 -w 2"
grep -q 'stran-root initial commit: phase=comb AND=3->2 gain=1' "$tmp_dir/helper_remap.log"
# q=1 is per root, not a global batch cap: all three roots contribute their
# complete direct frontier plus one Build candidate to the initial wave.
grep -q 'stran-root per-root candidates: discover-calls=3 total=6 max=3' "$tmp_dir/helper_remap.log"
grep -q 'batch-relations-max=6' "$tmp_dir/helper_remap.log"
grep -Eq 'stran-root cross-wave proof reuse: generation-skipped=[0-9]+ remapped=[1-9][0-9]* invalidated=[0-9]+ retained=[1-9][0-9]*' "$tmp_dir/helper_remap.log"
grep -q 'stran-root helper batch: enabled=yes retained=1 active=1 inactive=0 classes=1 endpoints=3 materialized-gates=1 obligations=3 relation-total=4' "$tmp_dir/helper_remap.log"
grep -q 'candidates=3 seeded=4 helper-seeds=1 proved=3 split=0 unknown=0' "$tmp_dir/helper_remap.log"
grep -q 'stran-root round commit: round=1 phase=seq AND=2->1 gain=1' "$tmp_dir/helper_remap.log"
grep -q 'stran-root rounds summary: configured=2 completed=2 comb-passes=1 comb-commits=1 seq-passes=2 seq-commits=1 AND=3->1 gain=2' "$tmp_dir/helper_remap.log"
test "$(grep -c 'phase=comb snapshot=immutable' "$tmp_dir/helper_remap.log")" -eq 1

# Historical command lines often spell out -t.  It remains accepted as a
# compatibility spelling and must not change the always-all scheduler.
run_case seq_t_compat test/stran_seq_only.blif "-t"
grep -q 'scheduler=per-root-q-all-candidates' "$tmp_dir/seq_t_compat.log"
grep -q 'q-build-per-root=1' "$tmp_dir/seq_t_compat.log"
grep -q 'AND=1->0 gain=1' "$tmp_dir/seq_t_compat.log"

# With an intentionally stopped oracle, UNKNOWN obligations are page-local;
# no failed portfolio may be committed and the unchanged graph exhausts once.
run_case seq_order_frontier test/stran_seq_order.blif "-S 0"
grep -Eq 'stran-root sequential relations: candidates=[1-9][0-9]* seeded=[1-9][0-9]* helper-seeds=0 proved=0 split=0 unknown=[1-9][0-9]*' "$tmp_dir/seq_order_frontier.log"
grep -q 'selected-roots=0 marginal-AND=0 cleanup-exact-AND=0 AND=1->1' "$tmp_dir/seq_order_frontier.log"

run_case seq_order_round_stop test/stran_seq_order.blif "-S 0 -w 2"
grep -q 'stran-root rounds summary: configured=2 completed=1 comb-passes=1 comb-commits=0 seq-passes=1 seq-commits=0 AND=1->1 gain=0' "$tmp_dir/seq_order_round_stop.log"

run_case seq_order_fixed_point test/stran_seq_order.blif "-S 0 -w 0"
grep -q 'stran-root rounds summary: configured=0 completed=1 comb-passes=1 comb-commits=0 seq-passes=1 seq-commits=0 AND=1->1 gain=0' "$tmp_dir/seq_order_fixed_point.log"

run_case seq_unknown test/stran_seq_only.blif "-S 0"
grep -Eq 'candidates=[1-9][0-9]* seeded=[1-9][0-9]* helper-seeds=[0-9]+ proved=0 split=0 unknown=[1-9][0-9]*' "$tmp_dir/seq_unknown.log"
grep -q 'selected-roots=0 marginal-AND=0 cleanup-exact-AND=0 AND=1->1' "$tmp_dir/seq_unknown.log"

run_case seq_round_stop test/stran_seq_only.blif "-S 0 -w 2"
grep -q 'stran-root rounds summary: configured=2 completed=1 comb-passes=1 comb-commits=0 seq-passes=1 seq-commits=0 AND=1->1 gain=0' "$tmp_dir/seq_round_stop.log"

# Regression for per-output UNKNOWN isolation.  With this small conflict limit,
# standard scorr produces UNKNOWN obligations while other speculative classes
# are still proved or split.  An UNKNOWN must never poison the complete batch.
if [[ -f benchmark/gen26.aig ]]; then
    mixed_unknown_log="$tmp_dir/mixed_unknown.log"
    "$abc_bin" -q "&read benchmark/gen26.aig; &write $tmp_dir/mixed_unknown-before.aig; &stran -P root -p -q 2 -w 2 -C 1; &write $tmp_dir/mixed_unknown-after.aig; dsec $tmp_dir/mixed_unknown-before.aig $tmp_dir/mixed_unknown-after.aig" >"$mixed_unknown_log"
    grep -q 'scheduler=per-root-q-all-candidates' "$mixed_unknown_log"
    grep -q 'invalid=0' "$mixed_unknown_log"
    grep -q 'Networks are equivalent' "$mixed_unknown_log"
else
    printf 'stran gen26 smoke: SKIP (benchmark/gen26.aig not present)\n'
fi

run_case proxy test/stran_proxy_roots.blif ""
grep -Eq 'stran-root sequential relations: candidates=[1-9][0-9]* seeded=[1-9][0-9]* helper-seeds=0 proved=[1-9][0-9]* split=0 unknown=0 roots=2' "$tmp_dir/proxy.log"
grep -q 'cleanup-exact-AND=2 AND=2->0' "$tmp_dir/proxy.log"

run_case polarity test/stran_polarity.blif "-l"
grep -Eq '^  COMB BUILD [0-9]+ [0-9]+ [0-9]+ 1 1 0$' "$tmp_dir/polarity.log"

# Build-only mode must suppress direct constant/existing discovery in every
# rebuilt phase while leaving both COMB Build and SEQ Build accounting intact.
run_case build_only test/stran_polarity.blif "-l -y"
grep -q 'candidates=build-only' "$tmp_dir/build_only.log"
grep -Eq '^  COMB BUILD [0-9]+ [0-9]+ [0-9]+ 1 1 0$' "$tmp_dir/build_only.log"
awk '
    /^  (COMB|SEQ) (CONSTANT|EXISTING) / {
        for (i=3; i<=8; i++) if ($i != 0) exit 1
        rows++
    }
    END { if (rows < 4) exit 1 }
' "$tmp_dir/build_only.log"

run_case q_cap test/stran_polarity.blif "-l -q 1"
grep -q 'candidates=constant/existing/build q-build-per-root=1' "$tmp_dir/q_cap.log"
grep -Eq 'stran-root resub iterator: initialized=[1-9][0-9]* .*q-wave-stops=[1-9]' "$tmp_dir/q_cap.log"

run_case q_unlimited test/stran_polarity.blif "-l -q 0 -w 1"
grep -q 'candidates=constant/existing/build q-build-per-root=0' "$tmp_dir/q_unlimited.log"
grep -Eq 'stran-root resub iterator: initialized=[1-9][0-9]* .*exhausted=[1-9][0-9]* q-wave-stops=0 snapshot-discarded=0 invalid=0' "$tmp_dir/q_unlimited.log"

run_case dirty test/stran_dirty.blif ""
grep -Eq 'stran-root dirty: root-free=[1-9]|root-MFFC-changed=[1-9]' "$tmp_dir/dirty.log"
grep -Eq 'stran-root cross-wave proof reuse: generation-skipped=[0-9]+ remapped=[1-9][0-9]* invalidated=[0-9]+ retained=[0-9]+' "$tmp_dir/dirty.log"

# A positive initial COM wave commits once.  All later passes are SEQ; COM is
# never re-run after the rebuild.
run_case dirty_rounds test/stran_dirty.blif "-w 2"
grep -q 'stran-root initial commit: phase=comb AND=3->1 gain=2' "$tmp_dir/dirty_rounds.log"
test "$(grep -c 'phase=comb snapshot=immutable' "$tmp_dir/dirty_rounds.log")" -eq 1
grep -q 'stran-root rounds summary: configured=2 completed=1 comb-passes=1 comb-commits=1 seq-passes=1 seq-commits=0 AND=3->1 gain=2' "$tmp_dir/dirty_rounds.log"

# A sequentially proved constant candidate used to assert while constructing
# its proof-only proxy, then could lose a latch during final cleanup.
run_case constant test/stran_constant.blif ""
grep -q '^  SEQ CONSTANT 0 1 1 1 1 0$' "$tmp_dir/constant.log"
grep -q 'cleanup-exact-AND=1 AND=1->0' "$tmp_dir/constant.log"

# The exact-MFFC divisor switch changes only divisor eligibility.  Both sides
# must remain formally equivalent, and the startup banner must expose the
# selected mode so batch experiments cannot silently mix configurations.
run_case mffc_off test/stran_polarity.blif "-M"
grep -q 'divisor-route=ranked-TFI-only mffc-divisors=off' "$tmp_dir/mffc_off.log"

# The existing sequential sample remains a representative mixed-discovery
# smoke test even when its final winner is discharged in COMB.
run_case seq_existing test/stran_seq.blif ""

# The batch CSV parser must understand the root-only schema=4 output.  This
# guards the failure mode where -p ran successfully but every profile column
# was written as N/A.
python3 - "$tmp_dir/polarity.log" "$tmp_dir/helper_remap.log" <<'PY'
import sys
from pathlib import Path

sys.path.insert(0, "scripts")
from bench_scorr_then_stran import parse_stran

profile = parse_stran(Path(sys.argv[1]).read_text(encoding="utf-8"))
assert profile["profile_schema"] == 4
assert isinstance(profile["profile_total_sec"], (int, float))
assert isinstance(profile["profile_resub_enum_sec"], (int, float))
for stage in ("comb", "seq"):
    for kind in ("constant", "existing", "constructed"):
        for metric in ("generated", "submitted", "proved", "selected"):
            assert isinstance(profile[f"{stage}_{kind}_{metric}"], int)
assert isinstance(profile["final_and_gain"], int)
assert profile["comb_constructed_selected"] == 1
assert profile["comb_constructed_and_gain"] == 1
assert profile["final_and_gain"] == 1

seq_profile = parse_stran(Path(sys.argv[2]).read_text(encoding="utf-8"))
for field in (
    "root_helper_retained_max", "root_helper_injected_events",
    "root_helper_inactive_events", "root_helper_materialized_gates",
    "root_new_proved", "root_history_proved_selected",
    "root_proof_waves", "root_wave_continuations",
    "root_seq_obligations", "root_seq_seeded", "root_seq_helper_seeds",
    "root_iterator_initialized", "root_iterator_exhausted",
    "root_iterator_snapshot_discarded",
):
    assert isinstance(seq_profile[field], int), field
assert seq_profile["root_helper_retained_max"] >= 1
assert seq_profile["root_helper_injected_events"] >= 1
assert seq_profile["root_seq_seeded"] == (
    seq_profile["root_seq_obligations"] + seq_profile["root_seq_helper_seeds"]
)
assert seq_profile["root_iterator_initialized"] == (
    seq_profile["root_iterator_exhausted"] +
    seq_profile["root_iterator_snapshot_discarded"]
)
PY

# scorr may legitimately remove every latch before &stran is invoked.  This is
# a successful no-op, not a batch-run failure.
noop_out="$tmp_dir/combinational-noop.log"
"$abc_bin" -q "read_blif test/stran_combinational_noop.blif; strash; &get; &stran -P root" >"$noop_out"
grep -q 'network is combinational; root-only sequential transduction is a no-op' "$noop_out"

printf 'stran root-only regression: PASS\n'
