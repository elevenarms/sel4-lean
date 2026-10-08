#!/usr/bin/env bash
# Regenerate ONE module with imports (as the sweep's first attempt does) and build it, showing errors.
#   scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/gen_one.sh SEL4/Kernel/Init.lhs Kernel_Init'
PY=~/c0/venv/bin/python
SRC=/scratch/c0/verification/l4v/spec/haskell/src
OUT=~/c0/sel4-lean/lean/Sel4Lean/Spec/Gen/Mod
ART=~/c0/sel4-lean/artifacts/w2
ALL=$(cd $SRC && find SEL4 Data \( -name "*.hs" -o -name "*.lhs" \) | grep -v -E "/(ARM|ARM_HYP|X64|AARCH64)(/|\.)" | sort)
ROOTS=""; for m in $ALL; do ROOTS="$ROOTS $SRC/$m"; done
(cd ~/c0/sel4-lean/tools/hs2lean && $PY full.py module $SRC --types $ROOTS --modules $SRC/$1 \
   --compiled "$ART/compile-status.txt" --gen-dir "$OUT" --namespace "Sel4Lean.Spec.M.$2" > "$OUT/$2.lean.tmp" 2>/tmp/gen_one.err) \
  && mv "$OUT/$2.lean.tmp" "$OUT/$2.lean" || { cat /tmp/gen_one.err; exit 1; }
tail -3 /tmp/gen_one.err
cd ~/c0/sel4-lean/lean && timeout 900 ~/.elan/bin/lake build "Sel4Lean.Spec.Gen.Mod.$2" 2>&1 | grep -E "^error: Sel4Lean" -A${CTX:-3} | head -${LINES_MAX:-80}
