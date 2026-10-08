#!/usr/bin/env bash
# W2 compile sweep: translate every module into Spec/Gen/Mod/<Name>.lean (own namespace) and build them all.
# Runs ON the instance after hs2lean.sh (which generates Types.lean).
#   scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/w2_compile_sweep.sh'
set -uo pipefail
# regenerate Types.lean (and the crawl slice) first: generated files are tracked in git, so a
# scripts/remote_push.sh from a laptop with stale copies overwrites them on the instance
bash ~/c0/sel4-lean/env/remote/hs2lean.sh > /dev/null 2>&1
PY=~/c0/venv/bin/python
SRC=/scratch/c0/verification/l4v/spec/haskell/src
OUT=~/c0/sel4-lean/lean/Sel4Lean/Spec/Gen/Mod
ART=~/c0/sel4-lean/artifacts/w2
mkdir -p "$OUT" "$ART"; rm -f "$OUT"/*.lean
ALL=$( (cd $SRC && find SEL4 Data \( -name "*.hs" -o -name "*.lhs" \) | grep -v -E "/(ARM|ARM_HYP|X64|AARCH64)(/|\.)"; echo SEL4.lhs) | sort)
ROOTS=""; for m in $ALL; do ROOTS="$ROOTS $SRC/$m"; done
: > "$ART/translate.log"
export PATH=~/.elan/bin:$PATH
# Single pass in dependency order: generate a module, build it, record the result, then move on. A module
# imports only providers that already built in this pass (no oscillation). If it fails with imports, it is
# regenerated stub-only (the pre-import form) and whichever version compiles is kept.
: > "$ART/compile-status.txt"; : > "$ART/compile.log"; : > "$ART/import-mode.txt"
ORDERED=$(cd ~/c0/sel4-lean/tools/hs2lean && $PY full.py order $SRC $(for m in $ALL; do echo $SRC/$m; done))
gen() {  # gen MODULE NAME COMPILED_FILE
  (cd ~/c0/sel4-lean/tools/hs2lean && $PY full.py module $SRC --types $ROOTS --modules $SRC/$1 \
      --compiled "$3" --gen-dir "$OUT" --namespace "Sel4Lean.Spec.M.$2" > "$OUT/$2.lean.tmp" 2>> "$ART/translate.log") \
    && mv "$OUT/$2.lean.tmp" "$OUT/$2.lean"
}
build() {  # build NAME -> 0 if it compiles
  (cd ~/c0/sel4-lean/lean && timeout 600 lake build "Sel4Lean.Spec.Gen.Mod.$1" >> "$ART/compile.log" 2>&1)
}
: > "$ART/none.txt"
for m in $ORDERED; do
  name=$(echo "$m" | sed -e 's#^SEL4/##' -e 's#\.l\?hs$##' -e 's#[/.]#_#g')
  gen "$m" "$name" "$ART/compile-status.txt" || { echo "✖ $name" >> "$ART/compile-status.txt"; continue; }
  if build "$name"; then echo "✔ $name" >> "$ART/compile-status.txt"; echo "imports $name" >> "$ART/import-mode.txt"; continue; fi
  gen "$m" "$name" "$ART/none.txt"
  if build "$name"; then echo "✔ $name" >> "$ART/compile-status.txt"; echo "stubs $name" >> "$ART/import-mode.txt"
  else echo "✖ $name" >> "$ART/compile-status.txt"; fi
done
sort -k2 -o "$ART/compile-status.txt" "$ART/compile-status.txt"
ok=$(grep -c "^✔" "$ART/compile-status.txt"); bad=$(grep -c "^✖" "$ART/compile-status.txt")
echo "with imports: $(grep -c '^imports' "$ART/import-mode.txt"), stub-only fallback: $(grep -c '^stubs' "$ART/import-mode.txt")"
echo "modules compiling: $ok / $((ok + bad))"
grep -E "^error: " "$ART/compile.log" | sed -E 's/^error: [^:]+:[0-9]+:[0-9]+: //' | cut -c1-60 | sort | uniq -c | sort -rn | head -15
