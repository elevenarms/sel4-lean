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
# Parallelism. Isabelle defaults each session to min(cores, 8) threads (multithreading.ML), which leaves
# 3/4 of this box idle, so set threads explicitly. JOBS=3 is the widest point of this test graph
# (ExecSpec | AInvs | HaskellKernel). Memory: each session <= ~10 GB ML heap + ~6 GB JVM, so 3 fit in 62 GB.
THREADS=${THREADS:-$(nproc)}
JOBS=${JOBS:-3}
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
export ISABELLE_BUILD_OPTS="-o threads='"$THREADS"'"
echo "== $(date -u) run_tests -j '"$JOBS"' threads='"$THREADS"': '"$TESTS"'"
./run_tests -j '"$JOBS"' -v --junit-report /out/junit-riscv64.xml '"$TESTS"'
'

nohup bash -c "
  echo \"== \$(date -u) start (host: \$(nproc) cores, \$(free -g | awk '/Mem/{print \$2}') GB)\"
  start=\$(date +%s)
  # utilisation sampler: one line per minute while the run is alive
  ( while sleep 60; do
      docker ps -q --filter name=c0-proofs | grep -q . || break
      read -r _ u n s i w _ < /proc/stat; sleep 1; read -r _ u2 n2 s2 i2 w2 _ < /proc/stat
      busy=\$(( (u2+n2+s2-u-n-s)*100 / (u2+n2+s2+i2+w2-u-n-s-i-w) ))
      echo \"stats: cpu \${busy}% busy, mem \$(free -g | awk '/Mem/{print \$3}')G used, load \$(cut -d' ' -f1 /proc/loadavg)\"
    done ) &
  docker run --rm --name c0-proofs --hostname in-container \
    -v /scratch/c0/verification:/host \
    -v /scratch/c0/isabelle-home:/root/.isabelle \
    -v $OUT:/out \
    -w /host trustworthysystems/l4v bash -c '$SCRIPT'
  rc=\$?
  echo \"EXIT=\$rc wall=\$(( \$(date +%s) - start ))s\"
  echo \"== \$(date -u) done\"
" >> "$LOG" 2>&1 </dev/null &
echo "started (pid $!); tests: $TESTS; log: $LOG"
