import Sel4Lean.Tactic.WPAttr
import Sel4Lean.Monad.Except

/-!
# `wp` and `wpsimp` (W1)

`wp` works backwards from the postcondition. At each step it tries, in order:
1. split a bind (`bind_wp`), leaving the continuation goal first so its precondition is computed first;
2. extra rules given inline: `wp [h₁, h₂]` (l4v `wp: h₁ h₂`);
3. rules tagged `@[wp_rule]`, most recently tagged first;
4. `split` / `simp only []`, which see through Lean's `do` join points
   (`let x ← match …` elaborates to `have __do_jp := …; match …`, see notes/c4-first-proofs.md).

Every rule is applied under `with_reducible`, so a rule fires only when the program's shape matches;
default-transparency `apply` unfolds definitions and can loop (it did, twice).
`wp` stops when no step applies and leaves the remaining goals.

`wpsimp [rules]` = open the precondition, `wp [rules]`, then `simp_all` the leftover implication.
-/

namespace Sel4Lean
open Lean Elab Tactic Meta NondetM

-- The core rules, in priority order (the last tagged is tried first).
attribute [wp_rule] ret_wp pure_wp get_wp put_wp gets_wp modify_wp fail_wp assertM_wp assertOpt_wp
  select_wp selectF_wp ite_wp returnOk_wp throwError_wp stateAssert_wp
-- Tried first: a postcondition that ignores the state passes through any program unchanged.
-- (Otherwise e.g. `assertM_wp` yields a precondition mentioning an earlier result, which an opaque
-- getter before it cannot establish.)
attribute [wp_rule] valid_const

/-- Run `t`; on failure restore the state and report `false`. -/
private def attempt (t : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try t; return true
  catch _ => s.restore; return false

/-- One `wp` step on the main goal. -/
def wpStep (extra : Array Term) : TacticM Unit := do
  -- a premise like `∀ x, ⟪P⟫ f x ⟪Q⟫` (from rules such as mapM_x_inv): introduce, then continue
  -- syntactic check only: `valid` itself unfolds to a ∀, and must not be introduced
  if (← instantiateMVars (← getMainTarget)).consumeMData.isForall then
    evalTactic (← `(tactic| intro)); return
  if ← attempt (evalTactic (← `(tactic| (with_reducible apply NondetM.bind_wp'; intro)))) then return
  if ← attempt (evalTactic (← `(tactic| (with_reducible apply NondetM.bind_wp; intro)))) then return
  if ← attempt (evalTactic (← `(tactic| (with_reducible apply NondetM.bindE_wp; intro)))) then return
  for t in extra do
    if ← attempt (evalTactic (← `(tactic| with_reducible apply $t))) then return
  for n in (wpRuleExt.getState (← getEnv)).reverse do
    if ← attempt (evalTactic (← `(tactic| with_reducible apply $(mkIdent n)))) then return
  if ← attempt (evalTactic (← `(tactic| split))) then return
  if ← attempt (evalTactic (← `(tactic| simp only []))) then return
  throwError "wp: no rule applies"

syntax (name := wpStepTac) "wp_step" (" [" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| wp_step $[[$ts,*]]?) => wpStep ((ts.map (·.getElems)).getD #[])

/-- l4v `wp`: compute weakest preconditions backwards using `@[wp_rule]` rules plus `[extra]`. -/
syntax (name := wpTac) "wp" (" [" term,* "]")? : tactic
macro_rules
  | `(tactic| wp $[[$ts,*]]?) => `(tactic| repeat' wp_step $[[$ts,*]]?)

/-- l4v `wpsimp`: `wp`, then discharge the precondition implication with `simp_all`. -/
syntax (name := wpsimpTac) "wpsimp" (" [" term,* "]")? : tactic
macro_rules
  | `(tactic| wpsimp $[[$ts,*]]?) =>
    `(tactic| (apply NondetM.hoare_pre; (focus wp $[[$ts,*]]?); all_goals (try intro s hs); all_goals (try simp_all)))

end Sel4Lean
