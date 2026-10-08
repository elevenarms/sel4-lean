#!/usr/bin/env bash
# Pull results produced on the instance back into the repo:
#   ~/c0/sel4-lean/artifacts/                  -> ./artifacts/
#   ~/c0/sel4-lean/lean/Sel4Lean/Exec/Gen/     -> ./lean/Sel4Lean/Exec/Gen/  (translator output, C3)
# Commit them from here; the instance holds no git credentials.
set -euo pipefail
cd "$(dirname "$0")/.."
HOST=$(grep -oE '[a-z]+@[A-Za-z0-9.-]+' aws_harbor.sh | head -1)
SSH="ssh -i keys/harbor.pem -o BatchMode=yes"
rsync -a -e "$SSH" "${HOST}:c0/sel4-lean/artifacts/" ./artifacts/
mkdir -p lean/Sel4Lean/Exec/Gen
rsync -a -e "$SSH" "${HOST}:c0/sel4-lean/lean/Sel4Lean/Exec/Gen/" ./lean/Sel4Lean/Exec/Gen/ 2>/dev/null || true
mkdir -p lean/Sel4Lean/Spec/Gen
rsync -a -e "$SSH" "${HOST}:c0/sel4-lean/lean/Sel4Lean/Spec/Gen/" ./lean/Sel4Lean/Spec/Gen/ 2>/dev/null || true
git status --short artifacts/ lean/Sel4Lean/Exec/Gen/ lean/Sel4Lean/Spec/Gen/
