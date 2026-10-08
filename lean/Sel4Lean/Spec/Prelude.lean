import Sel4Lean.Spec.Gen.Types
import Sel4Lean.Exec.Prelude
import Sel4Lean.Spec.HsPrelude

/-!
# Prelude for module-level translations over the real kernel state (hand-written, W2/W3)

`Sel4Lean.Spec.Gen.Types` holds the translated types, including `KernelState` and the monads.
Hand-written helpers for module translations go here.
-/

namespace Sel4Lean.Spec

-- `Kernel` and `UserMonad` are generated in `Gen/Types.lean` (W2), modelled as l4v's Isabelle does.

/-- ASIDs enumerate as their underlying words (for `assocs` over ASID-indexed tables). -/
instance : EnumH ASID := ⟨EnumH.enumAll.map ASID.ASID⟩

end Sel4Lean.Spec
