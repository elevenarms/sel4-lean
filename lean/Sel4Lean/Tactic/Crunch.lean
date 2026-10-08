import Sel4Lean.Tactic.WP

/-!
# `crunch` (W1): generate "f preserves P" lemmas for a list of functions (l4v `crunch`)

```
crunch (P : KernelState → Prop) (H : LeafPreserve P)
  getNotification setNotification … cancelSignal …
  for inv : P with [H.getObject, H.setObject, …]
```

For each function `f` (in the order given) this states and proves

    theorem f_inv (P) (H) : ∀ a₀ … aₙ, ⟪P⟫ (f a₀ … aₙ) ⟪fun _ => P⟫

by unfolding `f` and repeating `crunch_step` with: the `with [...]` rules, the lemmas already generated for
earlier functions (so list callees first, as l4v's crunch effectively requires), and invariant-style rules
(`bind_inv`, `ret_inv`, `ite_wp_same`, `fail_wp_any`, `assertM_inv`, `stateAssert_inv`, `mapM_x_inv`).
Unlike `wp`, every goal keeps the fixed shape `⟪P⟫ f ⟪fun _ => P⟫`, so there are no precondition
metavariables (with `wp`, `split` on a `match` left branches sharing one and unification failed).
Binders must be explicit `(x : T)`; the generated lemmas take them as arguments.
-/

namespace Sel4Lean
open Lean Elab Command Term Meta Tactic

private def attemptC (t : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try t; return true
  catch _ => s.restore; return false

/-- One `crunch` step: every goal has the fixed shape `⟪P⟫ f ⟪fun _ => P⟫`, so no metavariables. -/
def crunchStep (rules : Array Term) : TacticM Unit := do
  if (← instantiateMVars (← getMainTarget)).consumeMData.isForall then
    evalTactic (← `(tactic| intro)); return
  for r in #[← `(NondetM.bind_inv'), ← `(NondetM.bind_inv), ← `(NondetM.bindE_wp)] do
    if ← attemptC (evalTactic (← `(tactic| (with_reducible apply $r; intro)))) then return
  for r in rules do
    if ← attemptC (evalTactic (← `(tactic| with_reducible exact $r))) then return
    if ← attemptC (evalTactic (← `(tactic| with_reducible apply $r))) then return
  if ← attemptC (evalTactic (← `(tactic| split))) then return
  if ← attemptC (evalTactic (← `(tactic| simp only []))) then return
  throwError "crunch: no rule applies"

syntax (name := crunchStepTac) "crunch_step" " [" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| crunch_step [$ts,*]) => crunchStep ts.getElems

syntax (name := crunchCmd)
  "crunch " (ppSpace bracketedBinder)* (ppSpace ident)+ " for " ident " : " term
    (" with " "[" term,* "]")? : command

private def binderNames (bs : Array (TSyntax ``Parser.Term.bracketedBinder)) :
    CommandElabM (Array Ident) := do
  let mut out := #[]
  for b in bs do
    match b with
    | `(bracketedBinder| ($xs:ident* : $_)) => out := out ++ xs
    | _ => throwErrorAt b "crunch: only explicit binders `(x : T)` are supported"
  return out

@[command_elab crunchCmd] def elabCrunch : CommandElab := fun stx => do
  match stx with
  | `(crunch $bs:bracketedBinder* $fs:ident* for $nm:ident : $P:term $[with [$rs,*]]?) =>
    let names ← binderNames bs
    let userRules : Array Term := (rs.map (·.getElems)).getD #[]
    let invRules : Array Term := #[
      ← `(NondetM.ret_inv _), ← `(NondetM.pure_inv _), ← `(NondetM.ite_wp_same _),
      ← `(NondetM.fail_wp_any), ← `(NondetM.assertM_inv _), ← `(NondetM.stateAssert_inv _),
      ← `(NondetM.mapM_x_inv)]
    let mut prev : Array Term := #[]
    for f in fs do
      let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
      let info ← getConstInfo fn
      let arity ← liftTermElabM <| forallTelescope info.type fun xs _ => do
        let mut n := 0
        for x in xs do
          if (← x.fvarId!.getBinderInfo).isExplicit then n := n + 1
        return n
      let args : Array Ident := (Array.range arity).map fun i => mkIdent (Name.mkSimple s!"a{i}")
      let thm := mkIdent (Name.mkSimple s!"{fn.getString!}_{nm.getId}")
      let rules : Syntax.TSepArray `term "," := .ofElems (userRules ++ prev ++ invRules)
      let stmt ← if arity == 0 then
          `(NondetM.valid $P $f (fun _ => $P))
        else
          `(∀ $args*, NondetM.valid $P ($f $args*) (fun _ => $P))
      let cmd ← `(command|
        theorem $thm $bs* : $stmt := by
          intros
          unfold $f
          repeat' crunch_step [$rules,*])
      withRef f <| elabCommand cmd
      let prevApp ← `($thm $names*)
      prev := prev.push prevApp
  | _ => throwUnsupportedSyntax

end Sel4Lean
