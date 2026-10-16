#!/usr/bin/env bash
set -euo pipefail
ERS_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${COMPARATOR_TOOLS:?Set COMPARATOR_TOOLS to a fresh tool directory}"
test "$(uname -s)" = Linux
mkdir -p "$COMPARATOR_TOOLS/bin"
export PATH="$HOME/.elan/bin:$PATH"
read -r ERS_CMP ERS_EXPORT ERS_LANDRUN < <(python3 - "$ERS_ROOT/lean/comparator/pins.json" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]));print(p['comparator_commit'],p['lean4export_commit'],p['landrun_commit'])
PY
)
git clone --quiet https://github.com/zouuup/landrun.git "$COMPARATOR_TOOLS/landrun"
git -C "$COMPARATOR_TOOLS/landrun" checkout --quiet --detach "$ERS_LANDRUN"
(cd "$COMPARATOR_TOOLS/landrun" && go build -trimpath -o "$COMPARATOR_TOOLS/bin/landrun" ./cmd/landrun)
git clone --quiet https://github.com/leanprover/comparator.git "$COMPARATOR_TOOLS/comparator"
git -C "$COMPARATOR_TOOLS/comparator" checkout --quiet --detach "$ERS_CMP"
git clone --quiet https://github.com/leanprover/lean4export.git "$COMPARATOR_TOOLS/lean4export"
git -C "$COMPARATOR_TOOLS/lean4export" checkout --quiet --detach "$ERS_EXPORT"
python3 - "$ERS_ROOT/lean/comparator/pins.json" "$COMPARATOR_TOOLS" <<'PY'
from pathlib import Path
import json, sys
pins=json.load(open(sys.argv[1])); root=Path(sys.argv[2])
assert pins['lean_toolchain']=='leanprover/lean4:v4.33.1'
for name in ['comparator','lean4export']:
    toolchain=root/name/'lean-toolchain'
    expected=pins['toolchain_patches'][name]['upstream']
    if toolchain.read_text().strip()!=expected:
        raise SystemExit('Unexpected upstream toolchain: '+name)
    toolchain.write_text(pins['lean_toolchain']+'\n')
PY
cmp "$ERS_ROOT/lean/lean-toolchain" "$COMPARATOR_TOOLS/comparator/lean-toolchain"
cmp "$ERS_ROOT/lean/lean-toolchain" "$COMPARATOR_TOOLS/lean4export/lean-toolchain"
(cd "$COMPARATOR_TOOLS/comparator" && lake build comparator)
test "$(git -C "$COMPARATOR_TOOLS/comparator/.lake/packages/lean4export" rev-parse HEAD)" = "$ERS_EXPORT"
(cd "$COMPARATOR_TOOLS/lean4export" && lake build lean4export)
