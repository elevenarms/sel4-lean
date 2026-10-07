# C2: Lean foundations (monad, Hoare logic, corres)

Status: **complete** (2026-10-07). About 540 lines of library code plus 94 lines of tests. 37 theorems.
`lake build` takes about 1 s on the instance.

## What was ported

| Lean module | l4v source | Contents |
|---|---|---|
| `Sel4Lean/Monad/Nondet.lean` | `lib/Monads/nondet/Nondet_Monad.thy` | `NondetM σ α := σ → ((α × σ) → Prop) × Prop`; `ret`, `bind`, `get`, `put`, `gets`, `modify`, `fail`, `select`, `alternative`, `assertM`, `assertOpt`, `stateAssert`, `whenM`, `unlessM`, `condition`, `mapM_x`; `Monad` instance; monad laws |
| `Sel4Lean/Monad/VCG.lean` | `Nondet_VCG.thy`, `Nondet_No_Fail.thy` | `valid` (notation `⟪P⟫ f ⟪Q⟫`), `noFail`; pre/post rules; wp rules for every primitive plus `if`; `wp` and `wpsimp` tactics |
| `Sel4Lean/Monad/Except.lean` | exception layer of the above | `returnOk`, `throwError`, `liftE`, `bindE`, `catchE`, `validE` and their wp rules (`'e + 'a` → `Except ε α`) |
| `Sel4Lean/Corres.lean` | `lib/Corres_UL.thy` | `corresUnderlying` (definition verbatim), `corres_guard_imp`, `corres_return`, `corres_get`, `corres_put`, **`corres_split`** |
| `Sel4Lean/Test/*.lean` | | `wpsimp` on `do`-blocks; a toy refinement proved with `corres_split` (same shape as `cancelSignal_corres`) |

## Design decisions

- **Sets are predicates and failure is a `Prop`.** Core Lean has no `Set`; `(α × σ) → Prop` is the same thing.
  The no-Mathlib decision held: nothing here needed it.
- **A `Monad` instance gives `do`-notation.** Lean `do` now means l4v's nondeterministic `do … od`. Translated
  Haskell (C3) can keep the original's `do` structure without a translator rewriting it.
- **Renames forced by Lean:** `when`/`unless` → `whenM`/`unlessM` (keywords). `assert` → `assertM`
  (`assert` is a built-in `do` element in Lean 4.34). Triples use `⟪ ⟫` because `⦃ ⦄` are binder brackets.
- **`wp` is backward unification.** Each rule leaves the precondition open, and `apply` fills it in. Rules apply under
  `with_reducible`. Without it, `apply` unfolds `put`/`bind` or searches `Decidable ?c` for `ite_wp`, and
  `repeat'` spun until we killed it at 10 minutes. `env/remote/lean_build.sh` now has a time limit (300 s by default).

## Effort data for the crawl decision

| Item | l4v (Isabelle) | Lean port | Notes |
|---|---|---|---|
| Monad definitions | `Nondet_Monad.thy` 1 file | 180 lines | 1:1 definitions; laws proved by hand |
| `corres_split` | ~15 lines (built on `corres_underlying_split`) | 35 lines, self-contained | first build passed |
| `wp` | rule sets, combinators, `wp_pre`, `crunch` | ~15-line macro | enough for straight-line code. Missing: rule sets, `wp_once`, `crunch`, `corres` automation |

Most proofs compiled on the first or second build. Every failure came from Lean surface syntax (keywords,
notation precedence, `cases` substitution names), never from l4v's semantics.

## What C3/C4 will need next

- `wp` rules for kernel-object accessors (`getNotification`, `setNotification`, `setThreadState`), generated per type
  as l4v's `crunch` / `getObject_wp` do.
- `corres_cases` / `corres_gen_asm2` (used by `cancelSignal_corres`) and object-level `*_corres` lemmas.
- A `match` rule for `wp` (`case` in `cancelSignal`), or translated code that uses `if` + projections.
