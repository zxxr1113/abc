#!/usr/bin/env bash
set -euo pipefail

abc_bin="${ABC_BIN:-./abc}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

result=$("$abc_bin" -q "read_blif test/stran_context.blif; strash; write_aiger $tmp_dir/before.aig; &get; &stran -T 100 -D 8 -Q 1 -W 3 -C 1000 -f; &write $tmp_dir/after.aig; dsec $tmp_dir/before.aig $tmp_dir/after.aig")
printf '%s\n' "$result"
grep -q 'sig-checks=' <<<"$result"
grep -q 'Networks are equivalent' <<<"$result"
