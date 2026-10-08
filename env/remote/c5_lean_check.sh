#!/usr/bin/env bash
# C5: export the Lambdapi theories to Lean and try to compile them (run ON the instance after c5_dedukti.sh).
#   scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/c5_lean_check.sh'
set -uo pipefail
eval "$(opam env --switch=c5)"
export PATH=~/.elan/bin:$PATH
HERE=$(cd "$(dirname "$0")" && pwd)
EX=/scratch/c5/isabelle_dedukti/examples
P=/scratch/c5/leancheck
OUT=~/c0/sel4-lean/artifacts/c5
mkdir -p "$P/Isabelle" "$OUT"
cp "$HERE/c5/STTfa.lean" "$P/Isabelle/STTfa.lean"
cp ~/c0/sel4-lean/lean/lean-toolchain "$P/"
cat > "$P/lakefile.toml" <<'TOML'
name = "isabellecheck"
defaultTargets = ["Isabelle"]
[[lean_lib]]
name = "Isabelle"
TOML
THEORIES="Pure session_Pure Tools_Code_Generator HOL_Groups_wp_orphans HOL_HOL HOL_Orderings HOL_Groups"
: > "$OUT/lean-export.tsv"
PREV=""
cd "$EX"   # relative file names: the exporter derives the Lean namespace from the path
for f in $THEORIES; do
  raw=$(mktemp)
  lambdapi export -o stt_lean --encoding ../encoding.lp --renaming "$HERE/c5/lean-renaming.lp" $f.lp > "$raw" 2> "$OUT/$f.export.err"
  # Post-process (each is an exporter gap, recorded in notes/c5-dedukti-spike.md):
  #  - Lean needs imports first: hoist them above set_option/namespace
  #  - linter.style.* options exist only in Mathlib: drop them
  #  - lambdapi `require open X` is not translated: re-add `open` for STTfa and every imported theory
  #  - some `require`s are dropped too: import and open every earlier theory (the chain is linear)
  {
    echo "import Isabelle.STTfa"
    for g in $PREV; do echo "import Isabelle.$g"; done
    echo "open STTfa"
    for g in $PREV; do echo "open $g"; done
    grep -v '^import ' "$raw" | grep -v '^set_option linter\.style\.'
  } > "$P/Isabelle/$f.lean"
  PREV="$PREV $f"
  printf '%s\t%s bytes\t%s decls\t%s errors\n' "$f" "$(wc -c < "$P/Isabelle/$f.lean")" \
    "$(grep -cE '^(axiom|theorem|noncomputable def|def) ' "$P/Isabelle/$f.lean")" \
    "$(grep -c 'invalid' "$OUT/$f.export.err")" | tee -a "$OUT/lean-export.tsv"
done
{ for f in $THEORIES; do echo "import Isabelle.$f"; done; } > "$P/Isabelle.lean"
cd "$P"
rm -rf .lake/build/lib/lean/Isabelle
s=$(date +%s)
timeout 1500 lake build > "$OUT/lake-build.log" 2>&1; rc=$?
echo "lake build rc=$rc wall=$(( $(date +%s) - s ))s" | tee -a "$OUT/lean-export.tsv"
grep -E "^error|✖|✔" "$OUT/lake-build.log" | head -40
