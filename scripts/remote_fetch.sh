#!/usr/bin/env bash
# Pull results produced on the instance (~/c0/sel4-lean/artifacts) back into ./artifacts.
# Commit them from here; the instance holds no git credentials.
set -euo pipefail
cd "$(dirname "$0")/.."
HOST=$(grep -oE '[a-z]+@[A-Za-z0-9.-]+' aws_harbor.sh | head -1)
rsync -a -e "ssh -i keys/harbor.pem -o BatchMode=yes" "$HOST:c0/sel4-lean/artifacts/" ./artifacts/
git status --short artifacts/
