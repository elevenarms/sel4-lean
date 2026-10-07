import Sel4Lean.Corres

/-! Tests: a toy refinement proved with `corres_split`, the shape of `cancelSignal_corres`. -/

namespace Sel4Lean.Test
open NondetM

/-- Abstract counter. -/
def absIncr : NondetM Nat Unit := do
  let x ← get
  put (x + 1)

/-- Concrete counter: stores twice the abstract value. -/
def concIncr : NondetM Nat Unit := do
  let x ← get
  put (x + 2)

/-- State relation: concrete = 2 × abstract. -/
def sr (s s' : Nat) : Prop := s' = 2 * s

theorem incr_corres :
    corresUnderlying sr True True (fun _ _ => True) (fun _ => True) (fun _ => True) absIncr concIncr := by
  unfold absIncr concIncr
  refine corres_guard_imp
    (corres_split (P := fun _ => True) (P' := fun _ => True)
      (R := fun _ _ => True) (R' := fun _ _ => True)
      corres_get
      (fun rv rv' (hr : sr rv rv') => corres_put (by unfold sr at *; omega))
      valid_true valid_true)
    (fun _ _ => ⟨trivial, trivial⟩) (fun _ _ => ⟨trivial, trivial⟩)

end Sel4Lean.Test
