#!/usr/bin/env bash
# Copy this repo's tracked files to the instance at ~/c0/sel4-lean.
# Only git-tracked files are sent, so keys/ and aws_harbor.sh never leave this machine.
set -euo pipefail
cd "$(dirname "$0")/.."
HOST=$(grep -oE '[a-z]+@[A-Za-z0-9.-]+' aws_harbor.sh | head -1)
# Files produced on the instance (results, generated Lean) are never pushed back: a stale laptop copy
# would overwrite fresh output (this happened twice). They flow only instance -> laptop (remote_fetch.sh).
git ls-files -z | tr '\0' '\n' | grep -v -E '^artifacts/|/Gen/' | tr '\n' '\0' \
  | rsync -a --from0 --files-from=- -e "ssh -i keys/harbor.pem -o BatchMode=yes" ./ "$HOST:c0/sel4-lean/"
echo "pushed $(git ls-files | wc -l | tr -d ' ') tracked files to $HOST:~/c0/sel4-lean"
