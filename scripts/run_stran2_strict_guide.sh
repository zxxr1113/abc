#!/usr/bin/env bash
# Opt-in native strict construction: reachable CEX + complete empty-label
# polarity classification + auxiliary free-state observations (not CEX).
set -euo pipefail
SCRIPT_DIR="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"
STRICT_GUIDE="${STRICT_GUIDE:-1}"
STRICT_BOTH_POLARITIES="${STRICT_BOTH_POLARITIES:-1}"
for value in "$STRICT_GUIDE" "$STRICT_BOTH_POLARITIES"; do
    case "$value" in 0|1) ;; *) echo 'ERROR: STRICT_GUIDE and STRICT_BOTH_POLARITIES must be 0 or 1' >&2; exit 1 ;; esac
done
export ABC_STRICT_GUIDE="$STRICT_GUIDE"
export ABC_STRICT_BOTH_POLARITIES="$STRICT_BOTH_POLARITIES"
printf 'Native strict Build: both-polarities=%s auxiliary-free-state-signature=%s\n' \
    "$ABC_STRICT_BOTH_POLARITIES" "$ABC_STRICT_GUIDE"
exec bash "$SCRIPT_DIR/run_stran2_strict_cex.sh" "$@"
