# Goal

Full functional-correctness verification of seL4 in Lean 4, reached in three stages (crawl → walk → run).
The end state is a Lean theorem that seL4's C implementation refines its abstract specification.

See [ROADMAP.md](ROADMAP.md) for the stages, exit criteria, and open decisions.

## Approach

seL4's existing proof (l4v, Isabelle/HOL) is a refinement stack:

```
Abstract spec (hand-written Isabelle)
      ▲  refinement proofs (AInvs, Refine)
Executable spec (Haskell → Isabelle via haskell-translator)
      ▲  refinement proofs (CRefine)
C implementation (C-parser → Simpl, AutoCorres)
```

Porting it to Lean takes three pieces:

1. **Definitions.** Haskell → Lean for the executable spec, and Isabelle → Lean for the abstract spec.
   This is the HOL → dependent types translation.
2. **Proof infrastructure.** A Lean port of l4v's nondeterministic state monad, wp calculus, `corres`,
   and its automation (`wpsimp`, `crunch`, `corres_*`).
3. **Proofs.** Either translate them (Isabelle proof terms → Dedukti/Lambdapi → Lean) or re-prove them in
   Lean with AI help. The crawl stage decides which.

The haskell-translator (regex-style Python) is a weak point for *trust*, but it only covers the
middle layer. The proofs and their automation are the main cost.

## Scope decisions (current)

- **Target architecture:** RISCV64 (the smallest l4v architecture).
- **Upstream:** decide in crawl whether to track l4v master or port a pinned snapshot.
- **Trust base:** every unverified translator is part of what the result depends on. Record these explicitly per stage.

## References

**seL4 / l4v**
- Build/verify Docker environment: https://github.com/seL4/seL4-CAmkES-L4v-dockerfiles
- l4v proofs: https://github.com/seL4/l4v
- Haskell translator: https://github.com/seL4/l4v/tree/master/tools/haskell-translator

**Proof translation**
- Dedukti (shared proof format; Isabelle export exists): https://github.com/Deducteam/Dedukti

**Background / tooling**
- DHOL: Theorem Proving in Dependently-Typed HOL (Rothgang, Rabe, Benzmüller; CADE-29).
  Covers DHOL → HOL, the reverse direction; useful theory for the HOL ↔ dependent types mapping.
  https://arxiv.org/abs/2305.15382
- DSLean: type-correct interop between Lean 4 and external DSLs (Rowney, Ahuja, Avigad, Welleck).
  Candidate tool for pattern-based syntax mapping into Lean. https://arxiv.org/html/2602.18657v3
- Lisar: Isar-style declarative proofs in Lean (AI-authored proof of concept). Could host translated
  Isar proofs; less useful for l4v's mostly `apply`-style scripts. https://github.com/nomeata/lean-lisar
