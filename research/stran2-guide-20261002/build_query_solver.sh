#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 1 ]; then
  echo "usage: $0 OUTPUT_PATH" >&2
  exit 2
fi
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
abc_root=$(cd -- "$script_dir/../.." && pwd)
solver_out=$1
mkdir -p -- "$(dirname -- "$solver_out")"
make -C "$abc_root" ABC_USE_NO_READLINE=1 -j8 libabc.a
gcc -O2 -DABC_USE_STDINT_H=1 -DABC_USE_PTHREADS -I "$abc_root/src" \
  -c "$script_dir/seq_care_cut2/query_solver.c" -o "$solver_out.o"
g++ -o "$solver_out" "$solver_out.o" "$abc_root/libabc.a" -lm -ldl -lpthread
