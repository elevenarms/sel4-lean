#!/usr/bin/env bash
# Lean <-> Isabelle gate (W3): check the Lean spec against l4v's built executable spec (session ExecSpec)
# inside the l4v container. Needs the difftest's cases.tsv / lean.out (env/remote/w3_difftest.sh).
#   scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/w3_isagate.sh'
# Output in ~/c0/sel4-lean/artifacts/w3/isabelle/.
set -uo pipefail
PY=~/c0/venv/bin/python
R=~/c0/sel4-lean
G=/scratch/c0/verification/gate
W=$R/artifacts/w3
A=$W/isabelle
mkdir -p "$G" "$A"
cp $R/env/remote/isagate/* "$G"/
# 1. constants of ExecSpec (needs a first build to exist for the case mapping); 2. values of the cases
run_isa() {
  $R/env/remote/in_l4v.sh "export L4V_ARCH=RISCV64 GATE_OUT=/host/gate; \
    cd /host/gate && timeout 7200 /host/isabelle/bin/isabelle build -d /host/l4v -d /host/gate -v LeanGate" \
    > "$A/build.log" 2>&1
  echo "isabelle exit $?" >> "$A/build.log"
}
[ -f "$A/consts.tsv" ] || { printf 'theory Values imports Main begin end\n' > "$G/Values.thy"; run_isa; cp "$G/consts.tsv" "$A/"; }
(cd $R/tools/hs2lean && $PY isagate.py gen "$W" "$A/consts.tsv") > "$A/gen.log"
cp "$A/Values.thy" "$G/Values.thy"
run_isa
cp "$G"/*.tsv "$A"/
grep -E "^GATE|\*\*\*|isabelle exit" "$A/build.log" | head -20
# 3. Lean declarations, for the name-level correspondence
{ echo "import Sel4Lean"; for f in $R/lean/Sel4Lean/Spec/Gen/Mod/*.lean; do
    n=$(basename "$f" .lean); grep -qx "✔ $n" $R/artifacts/w2/compile-status.txt && echo "import Sel4Lean.Spec.Gen.Mod.$n"; done
  cat <<'LEAN'
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut out := ""
  for (n, _) in env.constants.toList do
    if (`Sel4Lean.Spec).isPrefixOf n && !n.isInternal && !n.isInternalDetail then
      let s := n.toString
      unless ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "ibelow",
              "binductionOn", "inj", "injEq", "sizeOf_spec", "ctorIdx", "eq_1", "eq_def"].contains (n.getString!) do
        out := out ++ s ++ "\n"
  IO.FS.writeFile "LEAN_NAMES_OUT" out
LEAN
} | sed "s#LEAN_NAMES_OUT#$A/lean-names.tsv#" > $R/lean/GateNames.lean
(cd $R/lean && timeout 1800 ~/.elan/bin/lake env lean GateNames.lean) > "$A/lean-names.log" 2>&1
rm -f $R/lean/GateNames.lean
(cd $R/tools/hs2lean && $PY isagate.py compare "$W" && $PY isagate.py names "$A/consts.tsv" "$A/lean-names.tsv" "$A/names.tsv") | tee "$A/summary.txt"
# re-adjudicate the GHC difftest with the Isabelle values (Lean = Isabelle != Haskell -> `l4v`)
(cd $R/tools/hs2lean && $PY difftest.py compare "$W") | tail -3 | tee -a "$A/summary.txt"
