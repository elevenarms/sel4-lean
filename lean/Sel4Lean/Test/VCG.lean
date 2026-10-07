import Sel4Lean.Monad.VCG

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
