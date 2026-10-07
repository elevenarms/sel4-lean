#!/usr/bin/env bash
# Build the Lean project on the instance (C1). Installs elan on first use; the toolchain version comes
# from lean/lean-toolchain. Runs ON the instance:
#   scripts/remote_push.sh && scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/lean_build.sh'
# Log: ~/c0/lean-build.log (streamed into project.log by scripts/watch_remote.sh)
set -euo pipefail
LOG=~/c0/lean-build.log
{
  echo "== $(date -u) lean build"
  if [ ! -x ~/.elan/bin/elan ]; then
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  fi
  export PATH=~/.elan/bin:$PATH
  cd ~/c0/sel4-lean/lean
  echo "toolchain: $(cat lean-toolchain)"
  start=$(date +%s)
  # time limit: a looping tactic (e.g. repeat' in wp) must not hang the box
  timeout ${LEAN_TIMEOUT:-300} lake build && rc=0 || rc=$?
  [ "$rc" = 124 ] && echo "TIMEOUT after ${LEAN_TIMEOUT:-300}s"
  echo "lean: $(lean --version)"
  echo "EXIT=$rc wall=$(( $(date +%s) - start ))s"
} >> "$LOG" 2>&1
tail -4 "$LOG"
