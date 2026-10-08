# Roadmap: seL4 verification in Lean

Three stages. Each one removes the risk that would sink the next. No stage starts until the previous
stage's exit criteria are met.

| Stage | Outcome | Key risk retired |
|---|---|---|
| Crawl | One refinement lemma checks in Lean, end to end, on a thin slice | Feasibility and cost; translate vs. re-prove |
| Walk | Lean proof that the executable spec refines the abstract spec (RISCV64) | Whether Lean's automation can match l4v's at scale |
| Run | Lean proof that the C kernel refines the abstract spec | C semantics in Lean |

---

## Crawl: prove the pipeline on a thin slice

**Goal:** show it works and measure what it costs before committing to the full port.

### C0. Reference environment
- [x] Build the l4v Docker image (seL4-CAmkES-L4v-dockerfiles). Confirm host architecture and RAM; images target x86_64.
- [x] Check out l4v and the seL4 sources at a pinned commit (see `env/remote/verification-pinned.xml`, `notes/c0-environment.md`).
- [x] Check the RISCV64 proof sessions (at least `ExecSpec`, `AInvs`, `Refine`) and record build times. All pass; 36 min wall (`notes/c0-environment.md`).
- [x] Run the haskell-translator; read its output and the skeleton files in `spec/design/skel` (see notes).

### C1. Lean project setup
- [x] Lean 4 + Lake project in `lean/` (lib `Sel4Lean`). **No Mathlib during crawl**: core Lean has `BitVec`, `omega`, `grind`, `simp`. Revisit in C2.
- [x] Toolchain pinned (`leanprover/lean4:v4.34.1`); builds on the instance (`env/remote/lean_build.sh`, 15 s). **No GitHub Actions for now** (decision 2026-10-07): all builds run on the instance.

### C2. Lean foundations library (port of l4v `lib/Monads`)
- [x] Nondeterministic state monad (with failure) and its basic laws.
- [x] Hoare triples (`valid`, `validE`) and the core wp rules.
- [x] `corres` definition and its basic composition rules (`corres_split`, `corres_guard_imp`, …).
- [x] A minimal `wp` tactic, so you can find out early what porting the automation involves. See `notes/c2-lean-foundations.md`.

### C3. Translators, applied to one subsystem
Slice chosen in C0: **notifications** (`Notification.lhs` ↔ `IpcCancel_A`/`Ipc_A`); first lemma `cancelSignal_corres`.
- [x] Haskell → Lean for the executable-spec slice: `tools/hs2lean` (tree-sitter-haskell). All 13 functions of `Notification.lhs` + 3 types generated, compiling unedited.
- [x] Isabelle → Lean for the matching abstract-spec definitions (by hand: `Abstract/IpcCancel.lean`).
- [x] Write down how each HOL feature is mapped (`notes/c3-translators.md`). Type classes, locales and
      type-level numerals not hit yet.
- [ ] Testing: run the Lean executable spec and the Haskell model on the same inputs and compare.
      **Deferred:** needs the kernel state model translated (stubs are opaque). Translator unit tests exist.

### C4. First proofs
- [x] Port one invariant-preservation lemma for the slice: `cancelSignal_simple` (over the generated code).
- [x] Port one `corres` lemma (abstract ↔ executable) for the slice: `cancelSignal_corres`.
- [~] Record hours and Lean-line/Isabelle-line ratio: done (`notes/c4-first-proofs.md`). Both proofs were AI-assisted,
      so the hand-written baseline is still missing.

### C5. Dedukti spike
- [x] Export a small Isabelle/HOL theory to Dedukti/Lambdapi: Pure + HOL/Orderings/Groups (stock Isabelle2025).
- [x] Get it into Lean: Lambdapi `export -o stt_lean` exists; with a concrete STTfa encoding + post-processing,
      8.5 MB of generated Lean checks in 245 s. Result is a deep embedding (HOL `bool`, not Lean `Prop`).
- [x] Measure proof-term size and export time; extrapolate to l4v's scale: not feasible today (GB-scale before
      HOL.Main; version mismatch; no term sharing). See `notes/c5-dedukti-spike.md`.

### Crawl exit criteria
- One abstract ↔ executable refinement lemma checks in Lean.
- The Lean model and the Haskell model agree on the test inputs.
- Measured cost numbers (hours per lemma, size ratio, automation gaps).
- **A written decision: translate proofs (Dedukti route) or re-prove them (AI-assisted).**
- A written list of everything the crawl result trusts.

---

## Walk: full abstract ↔ executable refinement (RISCV64)

Crawl closed 2026-10-08 with the decision **re-prove** (see Open decisions). Carried over from crawl: the C3 side-by-side
test (needs the kernel-state model, W3) and a hand-written proof baseline (optional).

### W1. Automation layer (critical path)
- [x] `[wp_rule]` attribute + `wp` tactic driven by it (l4v `[wp]` sets); extra rules as `wp [h₁, h₂]` (`Tactic/WP.lean`).
- [x] Join-point handling in `wp` (Lean `do` compiles `let x ← match …` into `have __do_jp …; match …`).
- [x] `wpsimp` on top; `cancelSignal_simple` is now `wpsimp [setThreadState_st_tcb]` + `simp [simple']`, like l4v's.
- [x] `crunch`: generate "f preserves P" lemmas for every function in a module (l4v: 629 uses in Refine alone).
      `Tactic/Crunch.lean`; one command covers all 12 generated notification functions (`Refine/NotificationCrunch.lean`).
- [ ] `corres` automation: `corres_split` driver, `corres_cases`, `corres_gen_asm`, a `corres` rule set.

### W2. Translators at full scale
- [x] hs2lean over all of `Structures.lhs`, then module by module; track coverage (functions translated / total).
      **Types done:** `tools/hs2lean/full.py types` translates the whole RISCV64 type closure of `Structures.lhs`
      (41 types, 0 stubs; pointer cycles as `mutual` blocks) into `Spec/Gen/Types.lean`, which compiles. Functions next.
      Extended to every module: **93 types**. Functions: **97.7% translate**; **59/61 modules compile** (58 importing each other's definitions), with
      **90.6%** (98.0% excluding the 2 deferred boot modules) of the 594 non-machine functions translated in compiling modules (99 machine-interface functions
      are opaque by design, as in l4v) (`notes/w2-translation.md`, `artifacts/w2/`).
      **Update (W3):** 62/62 modules compile, boot code (`Init.lhs`, `BootInfo.lhs`) and `SEL4.lhs` included; machine
      operations are l4v's (`MachineOps.thy`), 23 simulator-only functions remain opaque.
- [ ] Decide the translated-code shape for automation (explicit binds vs `do` sugar), based on W1.
- [ ] Isabelle → Lean for the abstract spec: hand-assisted first, then a tool if the volume demands it.

### W3. Kernel state model
- [x] Translate `KernelState`, `PSpace`, `getObject`/`setObject` instead of stubbing them (types: W2 closure;
      `getObject`/`setObject` via the hand-translated `PSpaceStorable`).
- [x] Side-by-side test: Lean executable spec vs the Haskell model on the same inputs (from C3).
      **Pure functions done:** 60/60 functions agree with GHC on 158 cases (`env/remote/w3_difftest.sh`,
      [notes](notes/w3-difftest.md)); it caught five translator bugs that compiled. Monadic functions next,
      once the machine state is modelled.
- [x] Machine state: `ksMachineState`, `doMachineOp` and the RISCV64 `MachineOps` as in l4v; approximations
      replaced (`asUser` via `selectF`, `assocs`, `deleteRange`) ([notes](notes/w3-difftest.md#machine-state-model)).
- [x] Real `PSpaceStorable` instances and object sizes (generated `objBitsKO` etc.); l4v's config overrides
      (`Kernel_Config.thy`: `physBase`, `timeSlice`, …) ([notes](notes/w3-difftest.md#object-sizes-and-configuration)).
- [x] **Interchangeable with l4v's Isabelle spec**: gate against l4v's built `ExecSpec` heap
      (`env/remote/w3_isagate.sh`): 1319/1319 constants matched by name, 60/60 functions agree with Isabelle's
      evaluation; l4v's skeleton overrides followed (105 dropped Haskell definitions ported or aliased)
      ([notes](notes/w3-isabelle-gate.md)).
- [x] Boot code: `Kernel/Init.lhs` in l4v's init monad; 62/62 modules compile.
- [ ] Extend the value gate: datatype arguments (capabilities, objects), then monadic functions on generated
      kernel states, evaluated in Isabelle and Lean.

### W4. Proofs
- [ ] Port the invariant definitions (`invs`, `invs'`), then AInvs and Refine, replacing assumptions in
      `CancelSignalAssumptions`-style structures with proofs, module by module.
- [ ] Re-run pipeline as upstream l4v changes (or a decision to freeze a snapshot).

**Exit:** a Lean theorem that the RISCV64 executable spec refines the abstract spec, with all invariants proved.

---

## Run: down to C, and beyond

- [ ] **C semantics decision:**
  - (a) Translate the Isabelle C-parser's Simpl output into Lean. What you trust stays comparable to l4v's.
  - (b) A Lean-native C frontend plus an AutoCorres equivalent. Cleaner, but a research project of its own.
- [ ] Port the C refinement proofs (CRefine).
- [ ] **Headline theorem:** the C kernel refines the abstract spec, in Lean.
- [ ] Later: the security properties (integrity, confidentiality), more architectures, binary-level verification.

---

## Open decisions

| Decision | Decide by | Notes |
|---|---|---|
| Translate vs. re-prove proofs | ~~End of crawl~~ **decided 2026-10-08: re-prove** | AI-assisted, following l4v proof structure; Dedukti kept as a side channel (`notes/c5-dedukti-spike.md`) |
| Track upstream vs. pinned snapshot | End of crawl | Affects how the translators are built |
| Mathlib dependency | ~~C1~~ decided: not during crawl | Revisit in C2 if the monad library wants `Set` theory |
| C semantics approach | Start of run | (a) vs (b) above |
| Licensing of translated proofs | Before publishing anything | Believed mostly GPL-2.0 / BSD; confirm before publishing |

## Risks

- **Scale.** The original functional-correctness proof took roughly 20+ person-years. This is a multi-year programme.
- **Automation parity.** If Lean can't match l4v's automation, porting costs grow beyond any estimate.
- **Upstream drift.** l4v keeps changing.
- **Trust base growth.** Every unverified translator adds to what the final result trusts.
