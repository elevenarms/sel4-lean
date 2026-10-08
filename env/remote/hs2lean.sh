#!/usr/bin/env bash
# C3: regenerate the translated Lean for the notifications slice. Runs ON the instance.
#   scripts/remote_push.sh && scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/hs2lean.sh'
# Output: ~/c0/sel4-lean/lean/Sel4Lean/Exec/Gen/*.lean (fetch with scripts/remote_fetch.sh, commit from the Mac)
set -euo pipefail
PY=~/c0/venv/bin/python
[ -x "$PY" ] || { python3 -m venv ~/c0/venv && ~/c0/venv/bin/pip install -q tree-sitter tree-sitter-haskell; }
L4V=/scratch/c0/verification/l4v
HS=$L4V/spec/haskell/src/SEL4
REV="$(git -C $L4V rev-parse --short HEAD)"
T=~/c0/sel4-lean/tools/hs2lean/hs2lean.py
OUT=~/c0/sel4-lean/lean/Sel4Lean/Exec/Gen
mkdir -p "$OUT"
TYPES="NTFN Notification ThreadState"   # dependency order
$PY $T --rev "$REV" types $HS/Object/Structures.lhs $TYPES > "$OUT/Structures.lean"
$PY $T --rev "$REV" module $HS/Object/Notification.lhs \
  --imports Sel4Lean.Exec.ThreadStubs --types $HS/Object/Structures.lhs $TYPES > "$OUT/Notification.lean"
wc -l "$OUT"/*.lean

# W2: full types closure from Structures (+ RISCV64 arch structures)
SPEC=~/c0/sel4-lean/lean/Sel4Lean/Spec/Gen
mkdir -p "$SPEC"
(cd ~/c0/sel4-lean/tools/hs2lean && $PY full.py types $L4V/spec/haskell/src \
   $HS/Object/Structures.lhs $HS/Object/Structures/RISCV64.hs \
   $HS/Model/StateData.lhs $HS/Model/StateData/RISCV64.hs $HS/Model/PSpace.lhs > "$SPEC/Types.lean")
wc -l "$SPEC"/*.lean
