# C4: First proofs on the slice

Status: **complete** (2026-10-07). Both lemmas are proved over the **generated, unedited** executable spec.
`#print axioms` (in `lean/Sel4Lean/Test/Axioms.lean`) shows only Lean's standard `propext` / `Quot.sound`. No `sorry`.

## The two lemmas

| Lemma | l4v source | Kind | l4v size | Lean size | Wall time to clean build |
|---|---|---|---|---|---|
| `cancelSignal_corres` | `IpcCancel_R.thy:307` | refinement (abstract ↔ executable) | 53 lines | 60 lines (+31 lines of assumptions) | ~8 min, 3 builds |
| `cancelSignal_simple` | `IpcCancel_R.thy:71` | invariant (Hoare triple on generated code) | 3 lines (`wpsimp`) | 14 lines | ~10 min, 4 builds (one 180 s timeout) |

Both were written with AI assistance (Claude), so there is no hand-written baseline yet. Times are elapsed
time, including remote builds on the instance (about 1 s each, plus a 2-minute timeout once).

## Trust base

`CancelSignalAssumptions` (in `Refine/IpcCancel.lean`) lists every l4v fact the corres proof assumes,
each with its source. Nothing else is assumed. The opaque stubs carry no information, so they can't make a
false statement provable.

| Assumed | l4v source |
|---|---|
| `getNotification_corres`, `setNotification_corres` | `KHeap_R.thy:904`, `:1742` |
| `setThreadState_corres` | `TcbAcc_R.thy:2931` |
| getters do not change state | `get_simple_ko_inv`, `getObject_inv` |
| `set_notification` preserves `tcb_at`, `pspace_aligned`, `pspace_distinct` | `set_simple_ko` wp rules |
| `invs` + blocked thread ⇒ the objects exist | `invs_valid_objs`, `st_tcb_at_tcb_at`, … |
| a thread blocked on a notification is in its queue | `sym_refs_st_tcb_atD'` |
| `setThreadState_st_tcb` (for `cancelSignal_simple`) | `TcbAcc_R.thy:3735` |

l4v's proof of `cancelSignal_corres` does the last two kinds of reasoning inline (`sym_refs`,
`valid_obj'`). Here they're hypotheses, so the Lean proof covers somewhat less ground than the 53 Isabelle
lines it replaces.

## What we learned

1. **The C2 library was enough.** `corres_split`, `corres_guard_imp` and one new lemma (`corres_gen_asm2`)
   carried the refinement proof, following l4v's proof step for step.
2. **Lean's `do` notation creates join points.** `let x ← match … with …` elaborates to
   `have __do_jp := fun x => rest; match … with | … => __do_jp …`. So the program is no longer a chain of binds,
   and `wp` must inline the join point and case-split the `match`. Isabelle's `do … od` never does this.
   **The real `wp` (walk) needs a join-point rule.** Alternatively, `hs2lean` could emit
   `bind (match …) (fun x => rest)` explicitly instead of `do`-sugar.
3. **`with_reducible` is required everywhere rules are applied by search.** A default-transparency
   `apply bind_wp'` unfolded non-bind programs and spun until the build's 180 s time limit cut it off. Same
   lesson as C2; worth a lint.
4. **Pointer tags cost a lemma.** Isabelle uses bare words for pointers on both sides; our generated spec has
   `PPtr α`. Relating queues needed `erase_map_toPtr` (erase commutes with tagging). Expect a family of these.
5. **Automation gap, measured.** l4v proves `cancelSignal_simple` with one `wpsimp` call. We needed a 5-way
   `repeat' (first …)` loop and hand-picked rules. Missing: a `[wp]` rule registry, join-point handling,
   `crunch`.

## Input to the translate-vs-re-prove decision (with C5)

- Re-proving by following l4v's proof was quick at this size (minutes per lemma). The structure of l4v's
  proof transferred directly, but the tactics didn't: every `apply` step needed a Lean counterpart or a hypothesis.
- The cost that will grow is **automation** (wp registry, `crunch`, `corres` tactics), not individual proofs.
- C5 (Dedukti spike) still has to say what mechanical translation would cost, before the crawl decision.
