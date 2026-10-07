# C0: Reference environment

Status: **reference proofs pass** (RISCV64 abstract ↔ executable stack checks in 36 min). C-side and translator read-through still open.

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

## RISCV64 reference run (2026-10-07)

`env/remote/run_proofs.sh` with the defaults: threads=32, `-j3`, `--scale-timeouts 8`.
**All tests passed in 2175 s (36 min) wall time.** Reports are in [`artifacts/c0/`](../artifacts/c0/).

| Session | Wall | CPU | Avg cores busy | Peak mem |
|---|---|---|---|---|
| Pure + HOL + Word_Lib | 6:08 | 29:56 | 4.9 (8 threads; before the threads fix) | 10.5 GB |
| Lib | 0:53 | 9:42 | 10.9 | 7.2 GB |
| ASpec (abstract spec) | 2:21 | 6:07 | 2.6 | 9.0 GB |
| ExecSpec (translated Haskell spec) | 3:02 | 9:52 | 3.3 | 9.3 GB |
| HaskellKernel (GHC build of the model) | 1:02 | 0:41 | n/a | 0.8 GB |
| AInvs (abstract invariants) | 8:20 | 1:19:53 | 9.6 | 18.6 GB |
| BaseRefine | 2:25 | 4:42 | 1.9 | 7.9 GB |
| **Refine** (abstract ↔ executable) | **20:30** | **2:51:04** | **8.3** | **21.6 GB** |

Times are from Isabelle's own `Finished` lines. The `run_tests` totals in the JUnit file add startup and heap loading.

**Parallelism ceiling.** Even with 32 threads, the big sessions average 8–11 cores busy. l4v's theories form long
import chains, so only a few proofs are available to run at once; more threads won't help. To fill the machine,
run independent sessions side by side (e.g. the C chain: CParser → CSpec → CBaseRefine → CRefine).
A Lean port with the same module structure would hit the same limit.

### What went wrong on the way (all fixed in `run_proofs.sh`)
1. Isabelle's default thread count is `min(cores, 8)` (`multithreading.ML:42`). Set via `ISABELLE_BUILD_OPTIONS` in the user
   settings, because some tests call `isabelle build` directly and bypass the Makefile's `ISABELLE_BUILD_OPTS`.
2. `run_tests` timeouts are **CPU-time** budgets. With 32 threads, Lib used its budget in 46 s of wall time. Fixed with `--scale-timeouts`.
3. HaskellKernel failed with "command not found": the image only puts GHC and stack on PATH in `/root/.bashrc`.

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
