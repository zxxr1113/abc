#!/usr/bin/env bash
set -euo pipefail

abc_bin="${ABC_BIN:-./abc}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

result=$("$abc_bin" -q "read_blif test/stran_context.blif; strash; write_aiger $tmp_dir/before.aig; &get; &stran -T 100 -D 8 -Q 1 -W 3 -C 1000 -f; &write $tmp_dir/after.aig; dsec $tmp_dir/before.aig $tmp_dir/after.aig")
printf '%s\n' "$result"
grep -q 'sig-checks=' <<<"$result"
grep -q 'Networks are equivalent' <<<"$result"

super_result=$("$abc_bin" -q "read_blif test/stran_supergate.blif; strash; write_aiger $tmp_dir/super-before.aig; &get; &stran -T 20 -D 6 -Q 1 -W 3 -C 100 -f; &write $tmp_dir/super-after.aig; dsec $tmp_dir/super-before.aig $tmp_dir/super-after.aig")
printf '%s\n' "$super_result"
grep -q 'sig-checks=' <<<"$super_result"
grep -q 'Networks are equivalent' <<<"$super_result"
