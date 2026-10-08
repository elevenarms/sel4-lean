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
ALL=$(cd $SRC && find SEL4 Data \( -name "*.hs" -o -name "*.lhs" \) | grep -v -E "/(ARM|ARM_HYP|X64|AARCH64)(/|\.)" | sort)
ROOTS=""; for m in $ALL; do ROOTS="$ROOTS $SRC/$m"; done
: > "$ART/translate.log"
TARGETS=""
for m in $ALL; do
  name=$(echo "$m" | sed -e 's#^SEL4/##' -e 's#\.l\?hs$##' -e 's#[/.]#_#g')
  (cd ~/c0/sel4-lean/tools/hs2lean && $PY full.py module $SRC --types $ROOTS --modules $SRC/$m \
      --namespace "Sel4Lean.Spec.M.$name" > "$OUT/$name.lean" 2>> "$ART/translate.log") || { rm -f "$OUT/$name.lean"; continue; }
  TARGETS="$TARGETS Sel4Lean.Spec.Gen.Mod.$name"
done
export PATH=~/.elan/bin:$PATH
cd ~/c0/sel4-lean/lean
timeout 1800 lake build $TARGETS > "$ART/compile.log" 2>&1
# ✔ = built, ⚠ = built with warnings (both compile), ✖ = failed
ok=$(grep -cE "^(✔|⚠) .*Built Sel4Lean\.Spec\.Gen\.Mod\." "$ART/compile.log")
bad=$(grep -cE "^✖ .*Building Sel4Lean\.Spec\.Gen\.Mod\." "$ART/compile.log")
echo "modules compiling: $ok / $((ok + bad))"
grep -E "Sel4Lean\.Spec\.Gen\.Mod\." "$ART/compile.log" | grep -E "^(✔|⚠|✖)" | sed -E 's/^(✔|⚠|✖) \[[0-9/]+\] (Built|Building) Sel4Lean.Spec.Gen.Mod.([A-Za-z0-9_]+).*/\1 \3/' | sed 's/^⚠/✔/' | sort -k2 > "$ART/compile-status.txt"
grep -E "^error: " "$ART/compile.log" | sed -E 's/^error: [^:]+:[0-9]+:[0-9]+: //' | cut -c1-60 | sort | uniq -c | sort -rn | head -15
