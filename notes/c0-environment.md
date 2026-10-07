# C0: Reference environment

Status: **in progress** (environment ready; proof runs not started)

## Machine

Shared AWS scratch instance, `c5ad.8xlarge` (Ubuntu 24.04, x86_64, 32 cores, 62 GB RAM).
Other projects' Docker images live on this box. Don't touch them.

| Storage | What | Measured write |
|---|---|---|
| EBS root (`/`, 256 GB) | Docker images, `~/c0` logs, repo copy at `~/c0/sel4-lean` | 139 MB/s (looks like gp3 default) |
| Local NVMe RAID0 (`/scratch`, 1.1 TB, `env/remote/scratch.sh`) | Sources, Isabelle heaps, build outputs | 474 MB/s (single stream) |

`/scratch` is **wiped when the instance stops** (a reboot keeps it). `setup.sh` rebuilds it in about 15 s.

Docker is **rootless**: container root maps to host `ubuntu`. So we run `trustworthysystems/l4v` directly
(`env/remote/in_l4v.sh`) and skip upstream's per-user image. That image's `chown -R` layer is 6.5 GB, and
building it took about 7.5 minutes, held back by EBS throughput.

## Pinned sources

Exact revisions are in [`env/remote/verification-pinned.xml`](../env/remote/verification-pinned.xml).

| Component | Revision | Date |
|---|---|---|
| seL4 | `6df0b6e` | 2026-10-04 |
| l4v | `ac4a36d` | 2026-10-07 |
| Isabelle | `e64f55a` (Isabelle2025-2, seL4 `ts-2025-2` branch) | 2026-01-17 |
| HOL4 / polyml / graph-refine | see manifest | (binary verification; not needed until run) |
| seL4-CAmkES-L4v-dockerfiles | `285ed69` | 2026-08-04 |

## Reproducing

From the Mac:

```sh
scripts/remote_push.sh                                    # copy tracked repo files to ~/c0/sel4-lean
scripts/remote.sh 'bash ~/c0/sel4-lean/env/remote/setup.sh'
scripts/remote.sh '~/c0/sel4-lean/env/remote/in_l4v.sh "cd /host/l4v && ./run_tests --help"'
```

Watch progress locally with `tail -f project.log` (`scripts/watch_remote.sh` must be running).

Results produced remotely go to `~/c0/sel4-lean/artifacts/`. Pull them back with `scripts/remote_fetch.sh`
and commit from the Mac. The instance holds no git credentials.

## Haskell spec and translator (first look)

- `spec/haskell/src`: 73 literate `.lhs` files (~16.9k lines). Architecture-specific code, including
  **RISCV64, is in plain `.hs` files**. For example `SEL4/Object/Structures/RISCV64.hs`.
- `tools/haskell-translator`: ~3.3k lines of Python (`lhs_pars.py`, `pars_skl.py`, `braces.py`, …),
  driven by `make_spec.sh`. It also takes hand-written inputs in `caseconvs`, `primrecs` and `supplied`.
- `spec/design/skel`: 49 generic Isabelle skeleton theories, plus per-arch dirs (`RISCV64/` has ~25).
  The skeletons are Isabelle text with insertion markers that the translator fills in. A Lean
  retarget needs Lean versions of every skeleton, as well as a new code generator.

## Log

- 2026-10-07: First image build failed (`make` missing on host). Installed it and rebuilt.
- 2026-10-07: Build was slow because of disk throughput, not CPU (EBS 139 MB/s). Moved the work to local NVMe RAID0 and
  dropped the per-user image. A fresh `setup.sh` (pinned sync) now takes 14 s.
