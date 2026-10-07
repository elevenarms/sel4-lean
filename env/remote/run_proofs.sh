#!/usr/bin/env bash
# C0: check the RISCV64 reference proofs in the l4v container. Runs ON the instance, in the background.
#
#   scripts/remote_push.sh && scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/run_proofs.sh'
#   scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/run_proofs.sh ExecSpec'   # subset
#
# Log:     ~/c0/proofs-riscv64.log (streamed into project.log by scripts/watch_remote.sh)
# Results: ~/c0/sel4-lean/artifacts/c0/ (fetch with scripts/remote_fetch.sh, commit from the Mac)
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
LOG=~/c0/proofs-riscv64.log
OUT=~/c0/sel4-lean/artifacts/c0
JOBS=${JOBS:-4}   # parallel sessions; each Isabelle session also uses many threads
TESTS=${*:-haskell-translator ASpec ExecSpec HaskellKernel AInvs Refine}
mkdir -p "$OUT"

# Mounted into the container at /root/.isabelle and /out
SCRIPT='
set -euo pipefail
cd /host/l4v
# One-time Isabelle setup (l4v docs/setup.md); persists in /scratch/c0/isabelle-home
if [ ! -f ~/.isabelle/etc/settings ]; then
  mkdir -p ~/.isabelle/etc && cp misc/etc/settings ~/.isabelle/etc/settings
fi
[ -f ~/.isabelle/.components-done ] || { /host/isabelle/bin/isabelle components -a && touch ~/.isabelle/.components-done; }
echo "== $(date -u) isabelle: $(/host/isabelle/bin/isabelle getenv -b ML_IDENTIFIER)"
export L4V_ARCH=RISCV64
echo "== $(date -u) run_tests -j '"$JOBS"' '"$TESTS"'"
./run_tests -j '"$JOBS"' -v --junit-report /out/junit-riscv64.xml '"$TESTS"'
'

nohup bash -c "
  echo \"== \$(date -u) start (host: \$(nproc) cores, \$(free -g | awk '/Mem/{print \$2}') GB)\"
  start=\$(date +%s)
  docker run --rm --hostname in-container \
    -v /scratch/c0/verification:/host \
    -v /scratch/c0/isabelle-home:/root/.isabelle \
    -v $OUT:/out \
    -w /host trustworthysystems/l4v bash -c '$SCRIPT'
  rc=\$?
  echo \"EXIT=\$rc wall=\$(( \$(date +%s) - start ))s\"
  echo \"== \$(date -u) done\"
" >> "$LOG" 2>&1 </dev/null &
echo "started (pid $!); tests: $TESTS; log: $LOG"
