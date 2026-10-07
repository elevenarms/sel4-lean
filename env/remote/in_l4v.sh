#!/usr/bin/env bash
# Run a command inside the l4v container. Mounts (all on local NVMe):
#   /scratch/c0/verification -> /host          (seL4, l4v, isabelle checkouts)
#   /scratch/c0/isabelle-home -> /root/.isabelle (Isabelle heaps and build state)
# Rootless Docker: container root == this host user, so outputs are owned by us.
#   env/remote/in_l4v.sh 'cd /host/l4v && ./run_tests --help'
set -euo pipefail
exec docker run --rm --hostname in-container \
  -v /scratch/c0/verification:/host \
  -v /scratch/c0/isabelle-home:/root/.isabelle \
  -w /host trustworthysystems/l4v bash -c "$*"
