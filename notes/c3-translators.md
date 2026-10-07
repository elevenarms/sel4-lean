# C3: Translators on the notifications slice

Status: **complete except the side-by-side test**, which waits on a translated kernel-state model (2026-10-07).

## What exists

| Piece | File | How it was made |
|---|---|---|
| Haskell → Lean translator | `tools/hs2lean/hs2lean.py` (~600 lines Python) | tree-sitter-haskell parser; strict: unsupported syntax stops it with node + line |
| Translator tests | `tools/hs2lean/test_hs2lean.py` | fixity re-association, refusal of ambiguous or unknown operators |
| Driver | `env/remote/hs2lean.sh` | regenerates from the pinned l4v checkout on the instance |
| Executable-spec types | `lean/Sel4Lean/Exec/Gen/Structures.lean` | **generated**: `NTFN`, `Notification`, `ThreadState` + selectors/setters |
| Executable-spec functions | `lean/Sel4Lean/Exec/Gen/Notification.lean` | **generated**: all 13 functions of `Notification.lhs`, unedited |
| Haskell basics | `lean/Sel4Lean/Exec/Prelude.lean` | hand-written: `Word`, `PPtr`, `fail`/`assert`/`forM_`/`delete` on `NondetM` |
| Out-of-slice stubs | `lean/Sel4Lean/Exec/Stubs.lean`, `ThreadStubs.lean` | hand-written `opaque` declarations (kernel state, TCB ops, `asUser`, …) |
| Abstract spec slice | `lean/Sel4Lean/Abstract/IpcCancel.lean` | hand-translated from Isabelle: `ntfn`, `notification`, `thread_state`, `cancel_signal` |

Everything builds on the instance (`lake build`, about 1 s for the whole library).

## Getting the generated Lean to compile

The translator needed four fixes before its output compiled. Every one came from Lean or tree-sitter
surface behaviour, not from the meaning of the kernel code:

1. Haskell comments inside `do` blocks show up as parse nodes. They're skipped now.
2. **Record construction was read as a record update.** tree-sitter puts the constructor where an update puts
   its base value.
3. **Nested `case` must be parenthesised.** Lean `match` alternatives are not layout-delimited, so an inner
   `match` swallowed the outer alternatives.
4. **Operator fixity.** tree-sitter nests every operator chain to the right. The translator flattens chains
   and re-associates them with Haskell's fixity table, and refuses unknown operators and the chains GHC
   would also reject.

After those, all 13 functions compiled unedited on the first Lean build.

## HOL / Haskell → Lean mapping (as used so far)

| Source feature | Lean | Notes |
|---|---|---|
| `nondet_monad` / Haskell `Kernel` | `NondetM KernelState` with `Monad` instance | Haskell `do` stays `do` |
| HOL types are non-empty | `opaque X : NonemptyType` for unknown types; `Inhabited` derived for datatypes | needed for `default`, `opaque` |
| `datatype` / multi-constructor `data` | `inductive` | |
| single-constructor record | `structure` | `{ x with f := v }` for update |
| partial Haskell selectors | total `def T.f` returning `default` on other constructors | matches Isabelle's underspecified selectors |
| record update on a multi-constructor type | generated `T.set_f`, a no-op on other constructors | matches Isabelle's generated update |
| `'a word` / `machine_word` / Haskell `Word` | `BitVec 64` | RISCV64 |
| `'a set` | predicate `α → Prop` | no Mathlib |
| `remove1` / `Data.List.delete` | `List.erase` | first occurrence, all three agree |
| `x { f = v }` patterns `C {}` | `.C ..` | |
| `fail "msg"`, `assert c "msg"` | `failH`, `assertH` (message dropped) | as l4v's `haskell_fail` / `haskell_assert` |
| Haskell `when`/`unless`/`assert` | `whenM`/`unlessM`/`assertM` | Lean keywords / `do` elements |

Not hit yet: type classes with overloading (Isabelle sorts), locales (per-architecture `arch_requalify`),
type-level numerals. They'll appear when the slice grows past notifications.

## Deferred

- **Side-by-side test** (Lean model vs Haskell model on the same inputs). With the kernel state opaque there
  is nothing to execute. This needs `KernelState`, `getObject`/`setObject` and the TCB operations translated,
  which means a large part of `Structures.lhs` and `SEL4.Model.PSpace`.
- **Isabelle → Lean automation.** The abstract side was translated by hand. The definitions are short and close to
  Lean already. An automated route (Isabelle export or the Dedukti spike, C5) is still open.
