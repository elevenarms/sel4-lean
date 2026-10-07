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
- [ ] Build the l4v Docker image (seL4-CAmkES-L4v-dockerfiles). Confirm host architecture and RAM; images target x86_64.
- [x] Check out l4v and the seL4 sources at a pinned commit (see `env/remote/verification-pinned.xml`, `notes/c0-environment.md`).
- [ ] Check the RISCV64 proof sessions (at least `ExecSpec`, `AInvs`, `Refine`) and record build times.
- [ ] Run the haskell-translator manually; read its output and the skeleton files in `spec/design/skel`.

### C1. Lean project setup
- [ ] Lean 4 + Lake project; decide whether to depend on Mathlib.
- [ ] Pin the toolchain; set up CI that builds the Lean project.

### C2. Lean foundations library (port of l4v `lib/Monads`)
- [ ] Nondeterministic state monad (with failure) and its basic laws.
- [ ] Hoare triples (`valid`, `validE`) and the core wp rules.
- [ ] `corres` definition and its basic composition rules.
- [ ] A minimal `wp` tactic, so you can find out early what porting the automation involves.

### C3. Translators, applied to one subsystem
Candidate slice: capability / CSpace operations. Choose the final slice after reading the specs in C0.
- [ ] Haskell → Lean for the executable-spec slice. Use a real Haskell parser (e.g. `ghc-lib-parser`), not regexes.
- [ ] Isabelle → Lean for the matching abstract-spec definitions (hand-assisted is fine).
- [ ] Write down how each HOL feature is mapped: non-empty types → `Inhabited`, type classes and sorts,
      locales, records, typedefs, `'a word` → `BitVec n`.
- [ ] Testing: run the Lean executable spec and the Haskell model on the same inputs and compare.

### C4. First proofs
- [ ] Port one invariant-preservation lemma for the slice.
- [ ] Port one `corres` lemma (abstract ↔ executable) for the slice.
- [ ] Do one by hand and one with AI assistance; record hours and Lean-line/Isabelle-line ratio.

### C5. Dedukti spike
- [ ] Export a small Isabelle/HOL theory to Dedukti/Lambdapi.
- [ ] Get it into Lean (find out whether a Lean exporter exists; otherwise estimate building one).
- [ ] Measure proof-term size and export time; extrapolate to l4v's scale.

### Crawl exit criteria
- One abstract ↔ executable refinement lemma checks in Lean.
- The Lean model and the Haskell model agree on the test inputs.
- Measured cost numbers (hours per lemma, size ratio, automation gaps).
- **A written decision: translate proofs (Dedukti route) or re-prove them (AI-assisted).**
- A written list of everything the crawl result trusts.

---

## Walk: full abstract ↔ executable refinement (RISCV64)

- [ ] Automate both translators so they cover the whole executable and abstract specs.
- [ ] Lean versions of l4v's automation: `wpsimp`, `crunch`, the `corres_*` family, the simp sets. **This is the critical path.**
- [ ] Port the abstract invariants (AInvs) and the executable-spec invariants.
- [ ] Port the abstract ↔ executable refinement proof (Refine).
- [ ] Pipeline that re-runs as upstream l4v changes (or a decision to freeze a snapshot).

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
| Translate vs. re-prove proofs | End of crawl | Based on C4/C5 data |
| Track upstream vs. pinned snapshot | End of crawl | Affects how the translators are built |
| Mathlib dependency | C1 | Gets you `BitVec` lemmas and automation; costs build time and version churn |
| C semantics approach | Start of run | (a) vs (b) above |
| Licensing of translated proofs | Before publishing anything | Believed mostly GPL-2.0 / BSD; confirm before publishing |

## Risks

- **Scale.** The original functional-correctness proof took roughly 20+ person-years. This is a multi-year programme.
- **Automation parity.** If Lean can't match l4v's automation, porting costs grow beyond any estimate.
- **Upstream drift.** l4v keeps changing.
- **Trust base growth.** Every unverified translator adds to what the final result trusts.
