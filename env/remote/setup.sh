#!/usr/bin/env bash
# C0 reference environment: seL4/l4v sources + l4v Docker image, pinned.
# Runs ON the instance (x86_64 Ubuntu, Docker available). Safe to re-run; done steps are skipped.
#
#   scripts/remote_push.sh && scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/setup.sh'
#
# Logs: ~/c0/repo-sync.log, ~/c0/image-build.log (streamed into project.log by scripts/watch_remote.sh)
set -euo pipefail

C0=~/c0
HERE=$(cd "$(dirname "$0")" && pwd)
DOCKERFILES_REV=285ed6985036e62e0db59cc92c242efcf60ae6e7   # seL4-CAmkES-L4v-dockerfiles, 2026-08-04
mkdir -p "$C0" ~/bin

# Host tools
command -v make >/dev/null || sudo -n apt-get install -y -q make
[ -x ~/bin/repo ] || { curl -sS https://storage.googleapis.com/git-repo-downloads/repo -o ~/bin/repo; chmod +x ~/bin/repo; }
git config --global user.name  >/dev/null || git config --global user.name  c0
git config --global user.email >/dev/null || git config --global user.email c0@localhost
git config --global color.ui false

# Sources at the pinned revisions (seL4, l4v, isabelle, HOL4, polyml, graph-refine)
mkdir -p "$C0/verification"
(
  cd "$C0/verification"
  echo "== $(date -u) repo sync (pinned)"
  [ -d .repo ] || ~/bin/repo init -u https://github.com/seL4/verification-manifest.git --depth=1
  cp "$HERE/verification-pinned.xml" .repo/manifests/pinned.xml
  ~/bin/repo init -m pinned.xml
  ~/bin/repo sync -j8 --force-sync
  echo "EXIT=0"
) >> "$C0/repo-sync.log" 2>&1

# Docker images: base l4v image from DockerHub + per-user image
if [ ! -d "$C0/seL4-CAmkES-L4v-dockerfiles" ]; then
  git clone -q https://github.com/seL4/seL4-CAmkES-L4v-dockerfiles.git "$C0/seL4-CAmkES-L4v-dockerfiles"
fi
git -C "$C0/seL4-CAmkES-L4v-dockerfiles" checkout -q "$DOCKERFILES_REV"
if ! docker image inspect user_img-"$(whoami)" >/dev/null 2>&1; then
  (
    echo "== $(date -u) image build"
    docker pull trustworthysystems/l4v
    make -C "$C0/seL4-CAmkES-L4v-dockerfiles" build_user_l4v
    echo "EXIT=0"
  ) >> "$C0/image-build.log" 2>&1
fi

echo "setup done: $(cd "$C0/verification" && for d in seL4 l4v isabelle; do printf '%s@%s ' "$d" "$(git -C "$d" rev-parse --short HEAD)"; done)"
