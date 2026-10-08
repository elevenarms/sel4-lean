# C5: Dedukti spike (Isabelle proofs → Dedukti/Lambdapi → Lean)

Status: **complete** (2026-10-08). The full pipeline runs end to end on Isabelle's foundational theories.
It doesn't scale to l4v.

## What ran

Separate from the l4v setup: stock **Isabelle2025** (isabelle_dedukti doesn't support l4v's Isabelle2025-2) with
`isabelle_dedukti` @ `925d138` (2026-07-01) and its HOL patch, plus **Lambdapi** built from source @ `22991e3`
(2026-10-03, includes recent Lean-export fixes). Scripts: `env/remote/c5_dedukti.sh`, `env/remote/c5_lean_check.sh`.

```
Isabelle2025 session HOL_Groups_wp (record_proofs=2)
   └─ isabelle dedukti_generate  ──▶  .lp files (Lambdapi)        lambdapi check: OK
        └─ lambdapi export -o stt_lean  ──▶  .lean files          lake build:     OK
```

| Step | Pure | HOL_Groups_wp (HOL, Orderings, Groups) |
|---|---|---|
| Isabelle build with proof recording | n/a | 27 s |
| Export to Lambdapi | 4 s, 41 KB | 16 s, 8.4 MB |
| Lambdapi check | 0 s | 1 s |
| Export to Lean | < 1 s | < 1 s each |
| **Lean kernel check** | 0.6 s | **HOL_HOL 52 s (2.0 MB), HOL_Orderings 102 s (2.5 MB), HOL_Groups 88 s (3.9 MB)** |

The Lean check covers 8.5 MB of generated Lean and took **245 s** in total (about 30 s per MB). Declarations:
Pure 23 axioms / 3 defs; HOL_HOL 21 / 26; HOL_Orderings 12 / 60; HOL_Groups 8 / 91. Proofs are emitted as
`def … : Prf … := <proof term>`, and Lean checks every one.

## What it took to get the Lean side to compile

The Lean exporter is new (fixes as recent as September–October 2026). Each item below is an exporter gap that
we worked around in post-processing:

1. **Rewrite rules are dropped.** `El (arr a b) ↪ El a → El b` and the `Prf` rules become plain axioms, so nothing
   type-checks. Fix: a concrete `STTfa.lean` (`El a := a`, `arr a b := a → b`, `Prf p := p`) turns the rules into
   definitional equalities.
2. **The `{|type|}` identifier** (Isabelle's `TYPE`) aborts the export silently mid-file. Fix: a renaming file.
3. **Name clashes with Lean core:** `trans`, `True`, `False`, `Not`. Fix: more renamings.
4. **`import` after `namespace`; Mathlib-only `set_option`s; `require open` dropped; absolute paths become
   namespaces.** Fixed in post-processing (`c5_lean_check.sh`).

## What the result is, and isn't

- **A deep embedding.** The theorems are about HOL's own `bool` (`El bool`, `Trueprop`, `eq_const`), not about
  Lean's `Prop`/`Eq`. To use them in `Sel4Lean`, a **bridge** is needed: map `bool` → `Prop`, `eq_const` → `Eq`,
  `The` → `Classical.choose`, …, and prove HOL's axioms (`refl`, `subst`, `ext`, `impI`, `mp`, `True_or_False`,
  `the_eq_trivial`, `eq_reflection`) from Lean definitions. That bridge doesn't exist yet. The Rocq route has
  the equivalent (`mappings.v`).
- **Trust:** what we trust is the Lean kernel plus those HOL axioms, plus definitions that Isabelle exports as
  axioms (overloaded definitions). A bridge would discharge the HOL axioms.

## Extrapolation to l4v

isabelle_dedukti's own measurements (32 threads, 128 GB): `HOL_Nat` 106 MB, `HOL_BNF_Def` 328 MB,
`HOL_Set_Interval` **1 GB** of Dedukti. **Nothing past `HOL.List` has been translated, so not even `HOL.Main`.**
l4v needs HOL-Main, HOL-Library and Word_Lib, then its own ~1M lines (`Refine` alone is 2 h 51 m of Isabelle CPU
time). Proof terms from `simp`/`auto`-heavy proofs are typically far larger than the source. Our Lean check rate
(about 30 s/MB) on TB-scale terms isn't plausible. Other blockers:

- **Version mismatch:** l4v is pinned to Isabelle2025-2 (seL4 fork); the exporter supports Isabelle2025.
- **Proof recording** (`record_proofs=2`) of every ancestor session, including l4v's, at l4v scale.
- **No term sharing** in the generated files (the exporter's README says so), which is the main source of blow-up.

**Conclusion: mechanical translation of l4v's proofs is not feasible with today's tools.** It works, and is trustworthy,
for small foundational libraries.

## Recommendation for the crawl decision

**Re-prove in Lean, following l4v's proof structure, with AI help** (C4 showed minutes per lemma at small size,
and the cost that grows is automation, not individual proofs). Keep the Dedukti route as a **side channel**:

- as a cross-check for specific foundational lemmas (e.g. Word_Lib facts) once a `bool → Prop` bridge exists;
- revisit if the exporter gains term sharing / modular export (Makarius Wenzel is reported to be improving
  Isabelle's proof-term export).
