#!/usr/bin/env bash
# Lean <-> Isabelle value gate on structured arguments (capabilities, objects, enums …): generate cases from
# the Lean types; evaluate in l4v's ExecSpec (Isabelle, chunked: one `isabelle process` per 10 cases, 6 in
# parallel, so a heap blow-up costs one chunk) and in Lean; compare as S-expressions.
#   scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/w3_isagate2.sh'
set -uo pipefail
PY=~/c0/venv/bin/python
R=~/c0/sel4-lean
G=/scratch/c0/verification/gate2
W=$R/artifacts/w3
A=$W/isa2
rm -rf "$G"; mkdir -p "$G/chunks" "$A"
(cd $R/tools/hs2lean && $PY isagate2.py gen "$W" "$W/isabelle/consts.tsv" "$R/lean/Sel4Lean/Spec/Gen/Mod" ${N:-6}) | tee "$A/gen.log"
cp $R/env/remote/isagate/Eval2.ML "$G/"
split -l ${CHUNK:-10} -d -a 3 "$A/isa-cases.tsv" "$G/chunks/c"
# one directory (ad hoc session) per chunk: Chunk.thy loads Eval2.ML on top of the ExecSpec heap
for c in "$G"/chunks/c*; do
  d="$c.d"; mkdir -p "$d"; mv "$c" "$d/cases.tsv"; cp "$G/Eval2.ML" "$d/"
  printf 'theory Chunk\n  imports ExecSpec.ArchIntermediate_H\nbegin\nML_file "Eval2.ML"\nend\n' > "$d/Chunk.thy"
done
$R/env/remote/in_l4v.sh "export L4V_ARCH=RISCV64; cd /host/gate2/chunks && ls -d *.d | xargs -P ${PAR:-6} -I{} sh -c \
  'GATE_CASES=/host/gate2/chunks/{}/cases.tsv GATE_RESULTS=/host/gate2/chunks/{}/out.tsv timeout 1800 \
   /host/isabelle/bin/isabelle process_theories -d /host/l4v -l ExecSpec -D /host/gate2/chunks/{} Chunk \
   > /host/gate2/chunks/{}/log 2>&1 || echo chunk {} failed'" > "$A/isabelle.log" 2>&1
cat "$G"/chunks/*.d/out.tsv > "$A/isabelle2.tsv" 2>/dev/null
echo "isabelle: $(wc -l < "$A/isabelle2.tsv") results, $(grep -c failed "$A/isabelle.log") chunks failed"
cp "$A/Gate2.lean" $R/lean/Gate2.lean
(cd $R/lean && timeout 2400 ~/.elan/bin/lake env lean Gate2.lean) > "$A/lean.out" 2>&1
rm -f $R/lean/Gate2.lean
(cd $R/tools/hs2lean && $PY isagate2.py compare "$W") | tee "$A/summary.txt"
