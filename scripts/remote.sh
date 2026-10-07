#!/usr/bin/env bash
# Run a command on the crawl scratch instance: scripts/remote.sh '<command>'
# Host and key come from the gitignored aws_harbor.sh and keys/ (not committed).
set -euo pipefail
cd "$(dirname "$0")/.."
HOST=$(grep -oE '[a-z]+@[A-Za-z0-9.-]+' aws_harbor.sh | head -1)
exec ssh -n -i keys/harbor.pem -o BatchMode=yes -o ServerAliveInterval=30 "$HOST" "$@"
