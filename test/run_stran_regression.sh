#!/usr/bin/env bash
set -euo pipefail

abc_bin="${ABC_BIN:-./abc}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

result=$("$abc_bin" -q "read_blif test/stran_context.blif; strash; write_aiger $tmp_dir/before.aig; &get; &stran -T 100 -D 8 -Q 1 -W 3 -C 1000 -f -p -P 2; &write $tmp_dir/after.aig; dsec $tmp_dir/before.aig $tmp_dir/after.aig")
printf '%s\n' "$result"
grep -q 'sig-checks=' <<<"$result"
grep -q 'Sequential transduction profile:' <<<"$result"
grep -q 'Sequential transduction proof profile:' <<<"$result"
grep -q 'Sequential transduction target aggregate:' <<<"$result"
grep -q 'Sequential transduction target profile:' <<<"$result"
grep -q 'Networks are equivalent' <<<"$result"

super_result=$("$abc_bin" -q "read_blif test/stran_supergate.blif; strash; write_aiger $tmp_dir/super-before.aig; &get; &stran -T 20 -D 6 -Q 1 -W 3 -C 100 -f; &write $tmp_dir/super-after.aig; dsec $tmp_dir/super-before.aig $tmp_dir/super-after.aig")
printf '%s\n' "$super_result"
grep -q 'sig-checks=' <<<"$super_result"
grep -q 'Networks are equivalent' <<<"$super_result"

multi_result=$("$abc_bin" -q "read_blif test/stran_multivictim.blif; strash; write_aiger $tmp_dir/multi-before.aig; &get; &stran -M 2 -G 2 -T 40 -D 8 -K 0 -Q 1 -W 3 -C 1000 -f; &write $tmp_dir/multi-after.aig; dsec $tmp_dir/multi-before.aig $tmp_dir/multi-after.aig")
printf '%s\n' "$multi_result"
grep -q 'victim-sets=' <<<"$multi_result"
grep -q 'accepted=1' <<<"$multi_result"
grep -q 'Networks are equivalent' <<<"$multi_result"

cegis_result=$("$abc_bin" -q "read_blif test/stran_cegis.blif; strash; write_aiger $tmp_dir/cegis-before.aig; &get; &stran -T 8 -N 1 -D 16 -K 0 -Q 1 -W 1 -A 0 -E 2 -R 1 -C 1000 -p -P 1; &write $tmp_dir/cegis-after.aig; dsec $tmp_dir/cegis-before.aig $tmp_dir/cegis-after.aig")
printf '%s\n' "$cegis_result"
grep -q 'Sequential transduction CEGIS profile: stored-cex=1 restarts=1 bmc=1 sat=1' <<<"$cegis_result"
grep -q 'Networks are equivalent' <<<"$cegis_result"
