#!/usr/bin/env bash
set -euo pipefail
PUB_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${COMPARATOR_TOOLS:?Run install-tools.sh first}"
mkdir -p "$PUB_ROOT/comparator-receipt"
python3 "$PUB_ROOT/lean/comparator/check-inputs.py" --receipt-dir "$PUB_ROOT/comparator-receipt"
CONFIG="$PUB_ROOT/lean/comparator.json"
if [ "$#" -gt 0 ]; then
  CONFIG="$(python3 "$PUB_ROOT/lean/comparator/comparison_groups.py" "$1" --receipt-dir "$PUB_ROOT/comparator-receipt")"
fi
cd "$PUB_ROOT/lean"
# Pinned upstream Comparator under real Linux Landlock and systemd restrictions.
sudo systemd-run --wait --collect --pipe --uid="$(id -u)" --gid="$(id -g)" \
  --property='RestrictAddressFamilies=~AF_UNIX' --property=NoNewPrivileges=yes \
  --property=RuntimeMaxSec=340min --working-directory="$PUB_ROOT/lean" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_TOOLS/bin/landrun" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export" \
  -- "$HOME/.elan/bin/lake" env stdbuf -oL -eL "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator" "$CONFIG" \
  2>&1 | tee "$PUB_ROOT/comparator-receipt/comparator.log"
grep -Fxq 'Lean default kernel accepts the solution' "$PUB_ROOT/comparator-receipt/comparator.log"
grep -Fxq 'Your solution is okay!' "$PUB_ROOT/comparator-receipt/comparator.log"
lake env lean FCAudit.lean > "$PUB_ROOT/comparator-receipt/axioms.log"
python3 comparator/check-axioms.py "$PUB_ROOT/comparator-receipt/axioms.log"
python3 "$PUB_ROOT/lean/comparator/check-inputs.py" --receipt-dir "$PUB_ROOT/comparator-receipt/after"
printf 'PASS\n' > "$PUB_ROOT/comparator-receipt/status.txt"
