#!/usr/bin/env bash
set -euo pipefail
test "$#" -eq 1 || { echo 'usage: build_solver.sh NEW_OUTPUT'; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec python3 -B "$here/build_solver.py" "$1"
