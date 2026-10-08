#!/usr/bin/env bash
# W3 differential test: the same pure functions, same inputs, in l4v's Haskell model (GHC) and generated Lean.
# Runs ON the instance after w2_compile_sweep.sh.   Results: ~/c0/sel4-lean/artifacts/w3/
set -uo pipefail
PY=~/c0/venv/bin/python
SRC=/scratch/c0/verification/l4v/spec/haskell/src
A=~/c0/sel4-lean/artifacts/w3
W=/scratch/c0/verification/difftest
mkdir -p "$A" "$W"
cd ~/c0/sel4-lean/tools/hs2lean
$PY difftest.py gen $SRC ~/c0/sel4-lean/artifacts/w2/compile-status.txt "$A" "${N:-8}"
cp "$A/Test.ghci" "$W/Test.ghci"
# Haskell: one REPL session over the RISCV64 build of the model
~/c0/sel4-lean/env/remote/in_l4v.sh "source /opt/ghcup/.ghcup/env; export STACK_ROOT=/etc/stack GHCUP_SKIP_UPDATE_CHECK=1; cd /host/l4v/spec/haskell && timeout 1200 stack exec -- ./stack-path cabal v2-repl --builddir=dist/riscv -v0 < /host/difftest/Test.ghci" > "$A/hs.out" 2>&1
# Lean: evaluate the generated definitions
cp "$A/DiffTest.lean" ~/c0/sel4-lean/lean/DiffTest.lean
(cd ~/c0/sel4-lean/lean && timeout 1200 ~/.elan/bin/lake env lean DiffTest.lean) > "$A/lean.out" 2>&1
rm -f ~/c0/sel4-lean/lean/DiffTest.lean
$PY difftest.py compare "$A"
