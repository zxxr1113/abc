#!/usr/bin/env bash
set -euo pipefail

abc_bin="${ABC_BIN:-./abc}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

resub_selftest=$("$abc_bin" -q '&stran_resub_test')
printf '%s\n' "$resub_selftest"
grep -q 'stran resub iterator/polarity/canonicalization self-test: PASS' <<<"$resub_selftest"

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
            rows++; selected += $6; marginal += $7
        }
        /stran-root effect totals:/ {
            for (i=1; i<=NF; i++) {
                if ($i ~ /^selected-roots=/) {split($i,a,"="); total_selected=a[2]+0}
                if ($i ~ /^marginal-AND=/) {split($i,a,"="); total_marginal=a[2]+0}
                if ($i ~ /^cleanup-exact-AND=/) {split($i,a,"="); exact=a[2]+0}
            }
        }
        /stran-root sequential relations:/ {
            for (i=1; i<=NF; i++) {
                if ($i ~ /^seeded=/) {split($i,a,"="); seeded=a[2]+0}
                if ($i ~ /^proved=/) {split($i,a,"="); proved=a[2]+0}
                if ($i ~ /^split=/) {split($i,a,"="); splitn=a[2]+0}
                if ($i ~ /^unknown=/) {split($i,a,"="); unknown=a[2]+0}
            }
        }
        /stran-root resub iterator:/ {
            for (i=1; i<=NF; i++) {
                if ($i ~ /^initialized=/) {split($i,a,"="); initialized=a[2]+0}
                if ($i ~ /^exhausted=/) {split($i,a,"="); exhausted=a[2]+0}
                if ($i ~ /^capped=/) {split($i,a,"="); capped=a[2]+0}
                if ($i ~ /^invalid=/) {split($i,a,"="); invalid=a[2]+0}
            }
        }
        END {
            if (rows != 6 || selected != total_selected ||
                marginal != total_marginal || marginal > exact ||
                seeded != proved + splitn + unknown ||
                initialized != exhausted + capped || invalid != 0) exit 1
        }
    ' "$out"
}

run_case comb test/stran_comb.blif ""
grep -q '^  COMB BUILD .* 1 1 1 1 0$' "$tmp_dir/comb.log"

run_case seq_top1 test/stran_seq_only.blif ""
grep -q 'seeded=1 proved=1 split=0 unknown=0 roots=1 class-max=2' "$tmp_dir/seq_top1.log"
grep -q '^  SEQ CONSTANT 0 0 0 0 0 0$' "$tmp_dir/seq_top1.log"
grep -q '^  SEQ EXISTING 0 1 1 1 1 0$' "$tmp_dir/seq_top1.log"

run_case seq_all test/stran_seq_only.blif "-t"
grep -q 'seeded=2 proved=2 split=0 unknown=0 roots=1 class-max=3' "$tmp_dir/seq_all.log"

# top-1 is the resub heuristic order, not a gain-first re-ranking: constant,
# then existing, then Build.  With one wave only the constant is submitted.
run_case seq_order_top1 test/stran_seq_order.blif "-S 0"
grep -q '^  SEQ CONSTANT 0 1 0 0 0 0$' "$tmp_dir/seq_order_top1.log"
grep -q '^  SEQ EXISTING 0 0 0 0 0 0$' "$tmp_dir/seq_order_top1.log"
grep -q 'seeded=1 proved=0 split=0 unknown=1' "$tmp_dir/seq_order_top1.log"

# The next wave keeps the unsubmitted ordered frontier.  It advances to an
# existing literal only after wave one retires the constant as TRIED_SEQ.
run_case seq_order_waves test/stran_seq_order.blif "-S 0 -w 2"
grep -q '^  SEQ CONSTANT 0 1 0 0 0 0$' "$tmp_dir/seq_order_waves.log"
grep -q '^  SEQ EXISTING 0 1 0 0 0 0$' "$tmp_dir/seq_order_waves.log"
grep -q 'seeded=2 proved=0 split=0 unknown=2' "$tmp_dir/seq_order_waves.log"

run_case seq_unknown test/stran_seq_only.blif "-S 0"
grep -q 'seeded=1 proved=0 split=0 unknown=1' "$tmp_dir/seq_unknown.log"
grep -q 'selected-roots=0 marginal-AND=0 cleanup-exact-AND=0 AND=1->1' "$tmp_dir/seq_unknown.log"

# A submitted top-1 relation releases its frontier slot even when the shared
# correspondence call stops early.  Wave two must therefore submit the other
# relation of the same root, never repeat wave one's candidate.
run_case seq_waves test/stran_seq_only.blif "-S 0 -w 2"
grep -q 'seeded=2 proved=0 split=0 unknown=2' "$tmp_dir/seq_waves.log"
grep -q 'stran-root waves: w1=1/0/1/0/0 w2=1/0/1/0/0' "$tmp_dir/seq_waves.log"

# Regression for per-output UNKNOWN isolation.  With this small conflict limit,
# standard scorr produces UNKNOWN obligations while other speculative classes
# are still proved or split.  An UNKNOWN must never poison the complete batch.
mixed_unknown_log="$tmp_dir/mixed_unknown.log"
"$abc_bin" -q "&read benchmark/gen26.aig; &write $tmp_dir/mixed_unknown-before.aig; &stran -P root -p -t -q 2 -C 1 -V 0; &write $tmp_dir/mixed_unknown-after.aig; dsec $tmp_dir/mixed_unknown-before.aig $tmp_dir/mixed_unknown-after.aig" >"$mixed_unknown_log"
grep -Eq 'stran-root scorr obligations: bmc=[0-9]+/[0-9]+/[1-9][0-9]*' "$mixed_unknown_log"
grep -Eq 'stran-root sequential relations: seeded=[0-9]+ proved=[1-9][0-9]* split=[0-9]+ unknown=0' "$mixed_unknown_log"
grep -q 'Networks are equivalent' "$mixed_unknown_log"

run_case proxy test/stran_proxy_roots.blif ""
grep -q 'seeded=2 proved=2 split=0 unknown=0 roots=2 class-max=2' "$tmp_dir/proxy.log"

run_case polarity test/stran_polarity.blif "-l"
grep -q '^  COMB BUILD .* 1 1 1 1 0$' "$tmp_dir/polarity.log"

run_case q_cap test/stran_polarity.blif "-l -q 1"
grep -q 'candidates=constant/existing/build q=1 divisor-route=TFI-only' "$tmp_dir/q_cap.log"
grep -Eq 'stran-root resub iterator: initialized=[1-9][0-9]* .*capped=[1-9]' "$tmp_dir/q_cap.log"

run_case dirty test/stran_dirty.blif ""
grep -Eq 'stran-root dirty: root-free=[1-9]|root-MFFC-changed=[1-9]' "$tmp_dir/dirty.log"

# A second wave must begin after stale roots/frontiers from wave one have been
# retired.  No candidate may be regenerated for the already released bundle.
run_case dirty_waves test/stran_dirty.blif "-w 2"
grep -q 'stran-root waves: .*w2=0/0/0/0/0' "$tmp_dir/dirty_waves.log"

# A sequentially proved constant candidate used to assert while constructing
# its proof-only proxy, then could lose a latch during final cleanup.
run_case constant test/stran_constant.blif ""
grep -q '^  SEQ CONSTANT 0 1 1 1 1 0$' "$tmp_dir/constant.log"
grep -q 'cleanup-exact-AND=1 AND=1->0' "$tmp_dir/constant.log"

run_case deprecated test/stran_comb.blif "-q 3 -L 1 -z -i -u -s"
grep -q -- '-L/-z/-i/-u/-s are deprecated and ignored' "$tmp_dir/deprecated.log"
grep -q 'candidates=constant/existing/build q=3 divisor-route=TFI-only' "$tmp_dir/deprecated.log"
grep -q 'AND=2->1' "$tmp_dir/deprecated.log"

# The existing sequential sample remains a representative mixed-discovery
# smoke test even when its final winner is discharged in COMB.
run_case seq_existing test/stran_seq.blif ""

# The batch CSV parser must understand the root-only schema=3 output.  This
# guards the failure mode where -p ran successfully but every profile column
# was written as N/A.
python3 - "$tmp_dir/polarity.log" <<'PY'
import sys
from pathlib import Path

sys.path.insert(0, "scripts")
from bench_scorr_then_stran import parse_stran

profile = parse_stran(Path(sys.argv[1]).read_text(encoding="utf-8"))
assert profile["profile_schema"] == 3
assert isinstance(profile["profile_total_sec"], (int, float))
assert isinstance(profile["profile_resub_enum_sec"], (int, float))
for stage in ("comb", "seq"):
    for kind in ("constant", "existing", "constructed"):
        for metric in ("generated", "submitted", "proved", "selected"):
            assert isinstance(profile[f"{stage}_{kind}_{metric}"], int)
assert isinstance(profile["final_and_gain"], int)
PY

# scorr may legitimately remove every latch before &stran is invoked.  This is
# a successful no-op, not a batch-run failure.
noop_out="$tmp_dir/combinational-noop.log"
"$abc_bin" -q "read_blif test/stran_combinational_noop.blif; strash; &get; &stran -P root" >"$noop_out"
grep -q 'network is combinational; root-only sequential transduction is a no-op' "$noop_out"

printf 'stran root-only regression: PASS\n'
