#!/usr/bin/env bash
# Run a command inside the l4v container, with ~/c0/verification mounted at /host.
#   env/remote/in_l4v.sh 'cd /host/l4v && ./run_tests --help'
set -euo pipefail
make -s -C ~/c0/seL4-CAmkES-L4v-dockerfiles user_run_l4v \
  HOST_DIR="$HOME/c0/verification" EXTRA_DOCKER_RUN_ARGS="-u $(id -u):$(id -g) --group-add stack" \
  EXEC="bash -c '$*'"
