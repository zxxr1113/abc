#!/usr/bin/env bash
set -euo pipefail

abc_bin="${ABC_BIN:-./abc}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

"$abc_bin" -q "read_blif test/stran_context.blif; strash; write_aiger $tmp_dir/before.aig; &get; &stran -T 100 -D 8 -C 1000; &write $tmp_dir/after.aig; dsec $tmp_dir/before.aig $tmp_dir/after.aig"
