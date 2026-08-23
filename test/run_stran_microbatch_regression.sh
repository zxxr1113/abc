#!/usr/bin/env bash
set -euo pipefail

abc_bin="${ABC_BIN:-./abc}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

selftest="$($abc_bin -q '&stran_resub_test')"
grep -q 'stran resub iterator/polarity/canonicalization/MFFC self-test: PASS' <<<"$selftest"

micro_log="$tmp_dir/micro.log"
"$abc_bin" -q "read_blif test/stran_microbatch_helper.blif; strash; write_aiger $tmp_dir/before.aig; &get; &stran -P root -p -y -q 0 -j 1 -w 1; &write $tmp_dir/after.aig; dsec $tmp_dir/before.aig $tmp_dir/after.aig" >"$micro_log"

grep -q 'selection=deferred-q-horizon-root-loss-gwmin' "$micro_log"
grep -q 'proof-build-batch-per-root=1' "$micro_log"
grep -q 'stran-root helper batch: enabled=yes retained=0 active=0 .* obligations=1 relation-total=1' "$micro_log"
grep -q 'stran-root helper batch: enabled=yes retained=1 active=1 .* obligations=1 relation-total=2' "$micro_log"
grep -q 'stran-root sequential relations: candidates=2 seeded=3 helper-seeds=1 proved=2 split=0 unknown=0' "$micro_log"
grep -q 'stran-root proof micro-batch summary: proof-waves=2 proof-calls=2 build-accepted-total=2 build-accepted-max-per-root=2 .* selected-after-stop=1' "$micro_log"
grep -q 'stran-root immutable frontier reuse: refresh-calls=1 refresh-reuses=1 page-candidates=2 known-candidate-scans-avoided=1' "$micro_log"
grep -q 'Networks are equivalent' "$micro_log"

# COM is a separate, fixed q=4 policy: it ignores the requested SEQ q/j,
# performs exactly one shared proof call, and reaches selection immediately.
awk '
    /phase=comb snapshot=immutable/ {
        in_comb=1
        if ($0 !~ /selection=commit-wave-root-loss-gwmin/ ||
            $0 !~ /q-build-per-root=4/ ||
            $0 !~ /proof-build-batch-per-root=0/) exit 1
    }
    in_comb && /stran-root wave portfolio:/ {
        if ($0 !~ /waves=1/ || $0 !~ /proof-calls=1/) exit 1
        checked=1
        in_comb=0
    }
    END { if (!checked) exit 1 }
' "$micro_log"

# The first SEQ selection must occur only after both proof batches.  This also
# guards against accidentally restoring the old "commit on first proof" path.
awk '
    /phase=seq snapshot=immutable/ { in_seq=1 }
    in_seq && /stran-root helper batch:/ { helper_batches++ }
    in_seq && /stran-root commit selection:/ && !seen_selection {
        if (helper_batches != 2) exit 1
        seen_selection=1
    }
    END { if (!seen_selection) exit 1 }
' "$micro_log"

legacy_log="$tmp_dir/legacy.log"
"$abc_bin" -q 'read_blif test/stran_microbatch_helper.blif; strash; &get; &stran -P root -y -q 1 -w 1' >"$legacy_log"
grep -q 'selection=commit-wave-root-loss-gwmin' "$legacy_log"
grep -q 'proof-build-batch-per-root=0' "$legacy_log"
if grep -q 'proof micro-batching: enabled=yes' "$legacy_log"; then
    exit 1
fi

printf 'stran proof micro-batch regression: PASS\n'
