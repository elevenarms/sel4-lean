import Sel4Lean.Tactic.WP

/-! Tests: `wp` / `wpsimp` on `do`-blocks over `NondetM`. -/

namespace Sel4Lean.Test
open NondetM

/-- `do`-notation here means l4v's nondeterministic `do … od`. -/
def incr : NondetM Nat Unit := do
  let x ← get
  put (x + 1)

example : ⟪fun _ => True⟫ incr ⟪fun _ s => s > 0⟫ := by
  unfold incr; wpsimp

def guardedIncr : NondetM Nat Unit := do
  let x ← get
  assertM (x < 10)
  put (x + 1)

example : ⟪fun s => s < 10⟫ guardedIncr ⟪fun _ s => s ≤ 10⟫ := by
  unfold guardedIncr; wpsimp; omega

/-- Nondeterminism: pick any value below the current state; every outcome stays below it. -/
def pickBelow : NondetM Nat Nat := do
  let n ← get
  select (fun x => x < n)

example : ⟪fun _ => True⟫ pickBelow ⟪fun r s => r < s⟫ := by
  unfold pickBelow; wpsimp

def branch (b : Bool) : NondetM Nat Unit := do
  if b then modify (· + 2) else modify (· + 1)

example (b : Bool) : ⟪fun s => s = 5⟫ (branch b) ⟪fun _ s => s ≥ 6⟫ := by
  unfold branch; wpsimp <;> omega

end Sel4Lean.Test

/-! Exception monad: a lookup that throws when the key is missing. -/
namespace Sel4Lean.Test
open NondetM

def lookupE (k : Nat) : NondetM (List (Nat × Nat)) (Except String Nat) :=
  bindE (liftE get) fun st =>
    match st.lookup k with
    | some v => returnOk v
    | none => NondetM.throwError "missing"

/-- On a state where `k ↦ 7`, the lookup succeeds with 7 and never reaches the error branch. -/
example : validE (fun st => st.lookup 3 = some 7) (lookupE 3) (fun r _ => r = 7) (fun _ _ => False) := by
  unfold lookupE
  refine bindE_wp (B := fun st s => st = s ∧ s.lookup 3 = some 7) ?_ ?_
  · intro st
    intro s ⟨hst, hk⟩ r s' hr
    subst hst
    rw [hk] at hr
    cases hr
    rfl
  · exact liftE_wp _ (hoare_pre (get_wp _) (fun s h => ⟨rfl, h⟩))

end Sel4Lean.Test
