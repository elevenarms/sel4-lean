#!/usr/bin/env bash
# Stream filtered progress from the remote crawl jobs into ./project.log.
# Host + key come from the gitignored aws_harbor.sh / keys/ (not committed).
set -u
cd "$(dirname "$0")/.."
KEY=keys/harbor.pem
HOST=$(grep -oE '[a-z]+@[A-Za-z0-9.-]+' aws_harbor.sh | head -1)
LOG=project.log
REMOTE_LOGS="~/c0/image-build.log ~/c0/repo-sync.log ~/c0/isabelle-setup.log ~/c0/proofs-riscv64.log"
echo $$ > .watch_remote.pid

ts() { date '+%H:%M:%S'; }
while true; do
  ssh -n -i "$KEY" -o BatchMode=yes -o ServerAliveInterval=30 -o ServerAliveCountMax=3 "$HOST" \
    "tail -n0 -F $REMOTE_LOGS 2>/dev/null" \
  | while IFS= read -r line; do
      case "$line" in
        "==> "*" <==") f=${line#==> }; f=${f% <==}; f=${f##*/}; f=${f%.log}; continue ;;
        ""|*"Pulling fs layer"*|*Waiting*|*"Verifying Checksum"*|*"Download complete"*|*Downloading*|*Extracting*|*"Pull complete"*|"#"[0-9]*" + "*) continue ;;
      esac
      echo "$(ts) [${f:-remote}] $line" >> "$LOG"
    done
  echo "$(ts) [watcher] ssh stream dropped; reconnecting in 15s" >> "$LOG"
  sleep 15
done
