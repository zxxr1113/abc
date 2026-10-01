#!/usr/bin/env bash
set -euo pipefail
test "$#" -eq 1 || { echo 'usage: build_query_model_solver.sh NEW_OUTPUT' >&2; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(cd -- "$here/../../.." && pwd)
test -f "$root/libabc.a" || { echo 'existing libabc.a required; no automatic make' >&2; exit 2; }
test ! -e "$1" && test ! -e "$1.o" || { echo 'refusing to overwrite an existing output' >&2; exit 2; }
mkdir -p -- "$(dirname -- "$1")"
gcc -O2 -DABC_USE_STDINT_H=1 -DABC_USE_PTHREADS -I "$root/src" -c "$here/query_model_solver.c" -o "$1.o"
g++ -o "$1" "$1.o" "$root/libabc.a" -lm -ldl -lpthread
