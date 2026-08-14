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
            }
        }
        END {
            if (rows != 6 || selected != total_selected ||
                marginal != total_marginal || marginal > exact ||
                seeded != proved + splitn + unknown ||
                initialized != exhausted) exit 1
        }
    ' "$out"
}

run_case comb test/stran_comb.blif ""
grep -q '^  COMB EXISTING .* 1 1 1 1 0$' "$tmp_dir/comb.log"

run_case seq_top1 test/stran_seq_only.blif ""
grep -q 'seeded=1 proved=1 split=0 unknown=0 roots=1 class-max=2' "$tmp_dir/seq_top1.log"

run_case seq_all test/stran_seq_only.blif "-t"
grep -q 'seeded=2 proved=2 split=0 unknown=0 roots=1 class-max=3' "$tmp_dir/seq_all.log"

run_case seq_unknown test/stran_seq_only.blif "-S 0"
grep -q 'seeded=1 proved=0 split=0 unknown=1' "$tmp_dir/seq_unknown.log"
grep -q 'selected-roots=0 marginal-AND=0 cleanup-exact-AND=0 AND=1->1' "$tmp_dir/seq_unknown.log"

run_case proxy test/stran_proxy_roots.blif ""
grep -q 'seeded=2 proved=2 split=0 unknown=0 roots=2 class-max=2' "$tmp_dir/proxy.log"

run_case polarity test/stran_polarity.blif "-l"
grep -q '^  COMB BUILD .* 1 1 1 1 0$' "$tmp_dir/polarity.log"

run_case dirty test/stran_dirty.blif ""
grep -Eq 'stran-root dirty: root-free=[1-9]|root-MFFC-changed=[1-9]' "$tmp_dir/dirty.log"

run_case deprecated test/stran_comb.blif "-q 99 -w 7 -L 1 -z -i -u -s"
grep -q -- '-q/-w/-L/-z/-i/-u/-s are deprecated and ignored' "$tmp_dir/deprecated.log"
grep -q 'AND=2->1' "$tmp_dir/deprecated.log"

# The existing sequential sample remains a representative mixed-discovery
# smoke test even when its final winner is discharged in COMB.
run_case seq_existing test/stran_seq.blif ""

printf 'stran root-only regression: PASS\n'
