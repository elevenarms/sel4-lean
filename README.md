# sel4-lean

Porting seL4's formal verification ([l4v](https://github.com/seL4/l4v), Isabelle/HOL) to **Lean 4**.
The end goal is a Lean theorem that seL4's C implementation refines its abstract specification.

**Status: crawl closed (2026-10-08), walk under way.** Decision: re-prove in Lean, following l4v's proofs.
The Isabelle reference passes on our hardware; Lean has l4v's monad, Hoare logic, `corres`, and `wp`/`wpsimp`/`crunch`
tactics; `cancelSignal_corres` is proved over generated code.

At spec scale the Lean executable spec is checked against **l4v's own built Isabelle spec** (session `ExecSpec`):
all **1319/1319** of its constants have a Lean counterpart of the same name, and all **60/60** testable functions
agree with Isabelle's evaluation, as do 74/79 functions over capabilities and kernel objects (429 cases, 0 differ).
All 51 constants l4v leaves unspecified are unspecified in Lean too. All **62/62** generated modules compile,
boot code included. Where l4v's
Isabelle differs from the Haskell model (it replaces 105 Haskell definitions by hand), the Lean follows Isabelle.
Getting there found real differences: `pptrUserTop`, `physBase`, the boot-time `foldME` order, and a CTE-in-TCB
case the earlier Lean port missed ([gate notes](notes/w3-isabelle-gate.md), [W3](notes/w3-difftest.md),
[W2](notes/w2-translation.md)). See [ROADMAP.md](ROADMAP.md).

## The idea

l4v proves seL4 correct as a stack of refinements:

```
  Abstract spec        hand-written Isabelle               (spec/abstract)
        ▲  Refine      ~5,300 lemmas, invariants (AInvs)
  Executable spec      Haskell model ──haskell-translator──▶ Isabelle   (spec/design)
        ▲  CRefine
  C implementation     C-parser → Simpl → AutoCorres
```

To move this to Lean we need:
1. **Definitions in Lean**: Haskell → Lean for the executable spec, Isabelle → Lean for the abstract spec
   (from HOL to dependent types).
2. **Proof infrastructure in Lean**: l4v's nondeterministic state monad, `wp` calculus, `corres`, and
   its automation (`wpsimp`, `crunch`).
3. **Proofs**: either translated (Isabelle → Dedukti → Lean) or re-proved with AI help. The crawl stage
   measures both and picks one.

We go in three stages: **crawl** (one slice end to end), **walk** (full abstract ↔ executable refinement),
**run** (down to C).

## Layout

| Path | What |
|---|---|
| [`GOAL.MD`](GOAL.MD) | Goal, approach, references |
| [`ROADMAP.md`](ROADMAP.md) | Crawl / walk / run tasks, exit criteria, open decisions, risks |
| [`notes/c0-environment.md`](notes/c0-environment.md) | C0 findings: environment, timings, translator read-through |
| [`notes/c2-lean-foundations.md`](notes/c2-lean-foundations.md) | C2: what was ported, design decisions, effort data |
| [`notes/c3-translators.md`](notes/c3-translators.md) | C3: translator, generated slice, HOL → Lean mapping |
| [`notes/c4-first-proofs.md`](notes/c4-first-proofs.md) | C4: first proofs, trust base, measurements |
| [`notes/c5-dedukti-spike.md`](notes/c5-dedukti-spike.md) | C5: Isabelle → Dedukti → Lean, results and extrapolation |
| [`notes/w2-translation.md`](notes/w2-translation.md) | W2: spec-wide translation, modelling decisions, numbers |
| [`tools/hs2lean/`](tools/hs2lean/) | Haskell → Lean translator (run with `env/remote/hs2lean.sh`) |
| [`lean/`](lean/) | Lean 4 project (`Sel4Lean`); build with `env/remote/lean_build.sh` |
| [`env/remote/`](env/remote/) | Reproducible reference environment (runs on an x86_64 Linux box) |
| [`artifacts/c0/`](artifacts/c0/) | Proof-run reports (JUnit) and summaries |
| [`scripts/`](scripts/) | Helpers for driving the remote box from a laptop |
| [`site/index.html`](site/index.html) | One-page project overview |

## Reproducing C0

The reference run needs an x86_64 Linux machine with Docker; we use 32 cores and 62 GB of RAM. Local NVMe helps.

```sh
# on the Linux box, with this repo at ~/c0/sel4-lean
bash env/remote/setup.sh        # NVMe /scratch, pinned seL4/l4v/Isabelle, l4v Docker image (~15 s + image pull)
bash env/remote/run_proofs.sh   # RISCV64: ASpec, ExecSpec, HaskellKernel, AInvs, Refine (~36 min)
tail -f ~/c0/proofs-riscv64.log
```

Pinned revisions are in [`env/remote/verification-pinned.xml`](env/remote/verification-pinned.xml):
seL4 `6df0b6e`, l4v `ac4a36d`, Isabelle2025-2.

From a Mac, `scripts/remote_push.sh`, `scripts/remote.sh` and `scripts/remote_fetch.sh` drive the box over ssh.
They expect a local, gitignored `aws_harbor.sh` and `keys/`. `scripts/watch_remote.sh` streams the remote
logs into `project.log`. Results are committed from the laptop; the remote box holds no git credentials.

## Licensing

l4v and seL4 are mostly GPL-2.0 / BSD-2-Clause. Translated definitions and proofs are probably derived works.
Check before publishing anything derived from them. This repo currently contains only our own scripts and notes.
