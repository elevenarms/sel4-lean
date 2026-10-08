#!/usr/bin/env bash
# C5 Dedukti spike: Isabelle proofs -> Dedukti/Lambdapi -> Lean, on the smallest sessions.
# Runs ON the instance, in the background:
#   scripts/remote_push.sh && scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/c5_dedukti.sh'
#   scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/c5_dedukti.sh stage_c'   # one stage
#
# Uses a separate stock Isabelle2025 (isabelle_dedukti does not support l4v's Isabelle2025-2).
# Log: ~/c0/c5-dedukti.log (streamed into project.log). Timings: ~/c0/sel4-lean/artifacts/c5/timings.tsv
set -uo pipefail

ISADK_REV=925d138fd433b1d04c270e166133ae7a673b18a9    # isabelle_dedukti master, 2026-07-01
LAMBDAPI_REV=22991e35a784e4fb3ac48f276fc769efd2e20619 # lambdapi master, 2026-10-03 (Lean export fixes)
ISABELLE_URL=https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux.tar.gz

W=/scratch/c5
OUT=~/c0/sel4-lean/artifacts/c5
LOG=~/c0/c5-dedukti.log
mkdir -p "$W" "$OUT"
export PATH="$W/Isabelle2025/bin:$HOME/.opam/c5/bin:$PATH"

t() {  # t NAME CMD... : run, log, record wall seconds
  local name=$1; shift
  echo "== $(date -u +%H:%M:%S) start $name"
  local s=$(date +%s)
  "$@"; local rc=$?
  local d=$(( $(date +%s) - s ))
  echo "== $(date -u +%H:%M:%S) done $name rc=$rc ${d}s"
  printf '%s\t%s\t%s\n' "$name" "$rc" "$d" >> "$OUT/timings.tsv"
  return $rc
}

stage_a() {  # Lambdapi from source via opam
  command -v opam >/dev/null || sudo -n apt-get install -y -q opam >/dev/null
  sudo -n apt-get install -y -q libev-dev libgmp-dev libssl-dev pkg-config >/dev/null   # lambdapi depexts
  [ -d ~/.opam ] || opam init -y --disable-sandboxing --bare
  opam switch list 2>/dev/null | grep -q '^\W*c5 ' || opam switch create c5 ocaml-base-compiler.5.2.1 -y
  eval "$(opam env --switch=c5)"
  [ -d "$W/lambdapi" ] || git clone -q https://github.com/Deducteam/lambdapi.git "$W/lambdapi"
  git -C "$W/lambdapi" checkout -q "$LAMBDAPI_REV"
  opam pin add -y -n lambdapi "$W/lambdapi"
  opam install -y -j "$(nproc)" lambdapi
  lambdapi --version
}

stage_b() {  # stock Isabelle2025 + isabelle_dedukti component + patched HOL
  if [ ! -x "$W/Isabelle2025/bin/isabelle" ]; then
    curl -sSfL "$ISABELLE_URL" -o "$W/isabelle2025.tar.gz" && tar -xzf "$W/isabelle2025.tar.gz" -C "$W"
  fi
  [ -d "$W/isabelle_dedukti" ] || git clone -q https://github.com/Deducteam/isabelle_dedukti.git "$W/isabelle_dedukti"
  git -C "$W/isabelle_dedukti" checkout -q "$ISADK_REV"
  if [ ! -f "$W/.hol-patched" ]; then
    chmod -R +w "$W/Isabelle2025/src/HOL"
    patch -s -up0 -d "$W/Isabelle2025/src/HOL/" < "$W/isabelle_dedukti/HOL.patch" && touch "$W/.hol-patched"
  fi
  isabelle components -u "$W/isabelle_dedukti"
  isabelle scala_build
  isabelle dedukti_generate -? 2>&1 | head -3 || true   # usage exits non-zero
}

stage_c() {  # export Pure and HOL_Groups_wp; check in Lambdapi; export to Lean
  eval "$(opam env --switch=c5)"
  local ex="$W/isabelle_dedukti/examples"
  cd "$ex"
  for S in Pure HOL_Groups_wp; do
    [ "$S" = Pure ] || t "isabelle_build_$S" make build SESSION=$S
    t "lp_$S" make lp SESSION=$S
    t "lpo_$S" make lpo SESSION=$S
  done
  ls -la "$ex"/*.lp | awk '{print $5"\t"$9}' > "$OUT/lp-sizes.tsv"
  mkdir -p "$W/lean-out"
  for f in session_Pure session_HOL_Groups_wp; do
    t "lean_export_$f" bash -c "lambdapi export -o stt_lean --encoding ../encoding.lp --renaming ../renaming.lp '$ex/$f.lp' > '$W/lean-out/$f.lean' 2> '$W/lean-out/$f.err'"
    wc -c "$W/lean-out/$f.lean" | tee -a "$OUT/lean-sizes.tsv"
    head -c 4000 "$W/lean-out/$f.lean" > "$OUT/$f.head.lean"
    tail -n 20 "$W/lean-out/$f.err" > "$OUT/$f.export.err" || true
  done
}

{
  echo "== $(date -u) C5 spike ($*)"
  if [ $# -gt 0 ]; then
    for s in "$@"; do t "$s" "$s"; done
  else
    t stage_a stage_a && t stage_b stage_b && t stage_c stage_c
  fi
  echo "EXIT=$? (C5)"
} >> "$LOG" 2>&1 &
echo "started C5 spike (pid $!); log: $LOG"
