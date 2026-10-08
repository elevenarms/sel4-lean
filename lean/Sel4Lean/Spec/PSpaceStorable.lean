import Sel4Lean.Spec.Prelude

/-!
# `PSpaceStorable`: typed access to the object heap (hand-written, W2/W3)

The Haskell spec's only user-defined type class (`Model/PSpace.lhs:56`) and its eight instances
(`Object/Instances.lhs`, `Object/Instances/RISCV64.hs`). It is translated by hand because it is a single
class, and because the Haskell version is polymorphic over `MonadFail m`, which Lean has no direct
counterpart for. The shape follows l4v's Isabelle `pspace_storable` class:
`projectKO_opt :: kernel_object ⇒ 'a option`, with failure in the nondeterministic monad.

No instance overrides `loadObject` / `updateObject`, so their Haskell default methods are plain functions
here. hs2lean leaves all names defined in this file to it (`full.py`: `PROVIDED`).
-/

namespace Sel4Lean.Spec
open Sel4Lean (NondetM)
open Sel4Lean.Exec (Word PPtr)

/-- Haskell `class PSpaceStorable a` (Model/PSpace.lhs:56). -/
class PSpaceStorable (a : Type) where
  makeObject : a
  injectKO : a → KernelObject
  /-- Haskell `projectKO :: MonadFail m => KernelObject -> m a`, as Isabelle's `projectKO_opt`. -/
  projectKO_opt : KernelObject → Option a

export PSpaceStorable (makeObject injectKO projectKO_opt)

/-- Haskell `objBitsKO` (Object/Structures.lhs:138): object size by kind. TODO(W2): use the generated
definition once modules import each other instead of stubbing. -/
opaque objBitsKO : KernelObject → Nat

/-- Haskell `objBits a = objBitsKO (injectKO a)` (Model/PSpace.lhs). -/
def objBits {a : Type} [PSpaceStorable a] (x : a) : Nat := objBitsKO (injectKO x)

/-- Haskell `projectKO` in a failing monad. -/
def projectKO {a σ : Type} [PSpaceStorable a] (o : KernelObject) : NondetM σ a :=
  match projectKO_opt o with
  | some x => pure x
  | none => NondetM.fail

/-- Haskell `mask n` at word type (Machine/RegisterSet.lhs:174). -/
abbrev maskW (n : Nat) : Word := (1 <<< n) - 1

/-- Haskell `alignError n = fail (…)` (Model/PSpace.lhs:308). -/
def alignError {α σ : Type} (_n : Nat) : NondetM σ α := NondetM.fail

/-- Haskell `typeError t o = fail (…)` (Model/PSpace.lhs:304). -/
def typeError {α σ : Type} (_t : String) (_o : KernelObject) : NondetM σ α := NondetM.fail

/-- Haskell `alignCheck x n = unless (x .&. mask n == 0) $ alignError n` (Model/PSpace.lhs:312). -/
def alignCheck {σ : Type} (x : Word) (n : Nat) : NondetM σ Unit :=
  if x &&& maskW n == 0 then pure () else NondetM.fail

/-- Haskell `sizeCheck` (Model/PSpace.lhs:315). -/
def sizeCheck {σ : Type} (start : Word) (next : Option Word) (n : Nat) : NondetM σ Unit :=
  match next with
  | none => pure ()
  | some e => if e - start < 1 <<< n then NondetM.fail else pure ()

/-- Haskell default method `loadObject` (Model/PSpace.lhs). -/
def loadObject {a σ : Type} [PSpaceStorable a] (ptr ptr' : Word) (next : Option Word)
    (obj : KernelObject) : NondetM σ a := do
  if ptr != ptr' then NondetM.fail
  let val ← projectKO obj
  alignCheck ptr (objBits val)
  sizeCheck ptr next (objBits val)
  pure val

/-- Haskell default method `updateObject` (Model/PSpace.lhs). The `projectKO oldObj` only checks the
old object has the same type. -/
def updateObject {a σ : Type} [PSpaceStorable a] (val : a) (oldObj : KernelObject) (ptr ptr' : Word)
    (next : Option Word) : NondetM σ KernelObject := do
  if ptr != ptr' then NondetM.fail
  let _ : a ← projectKO oldObj
  alignCheck ptr (objBits val)
  sizeCheck ptr next (objBits val)
  pure (injectKO val)

/-! ## Instances (Object/Instances.lhs, Object/Instances/RISCV64.hs) -/

/-- Haskell `nullMDBNode` (Object/Structures.lhs:348). TODO(W2): generated definition, as above. -/
opaque nullMDBNode : MDBNode
/-- Haskell `makeObject` for `TCB` (a 19-field record with `minBound`s, `timeSlice`, `newArchTCB`).
TODO(W2): generated definition, as above. -/
opaque makeObjectTCB : TCB
/-- Haskell `makeObject` for `ASIDPool` (`funPartialArray (const Nothing) …`). TODO(W2), as above. -/
opaque makeObjectASIDPool : ASIDPool

instance : PSpaceStorable Endpoint where
  makeObject := Endpoint.IdleEP
  injectKO := KernelObject.KOEndpoint
  projectKO_opt | .KOEndpoint e => some e | _ => none

instance : PSpaceStorable Notification where
  makeObject := Notification.NTFN NTFN.IdleNtfn none
  injectKO := KernelObject.KONotification
  projectKO_opt | .KONotification e => some e | _ => none

instance : PSpaceStorable CTE where
  makeObject := CTE.CTE Capability.NullCap nullMDBNode
  injectKO := KernelObject.KOCTE
  projectKO_opt | .KOCTE e => some e | _ => none

instance : PSpaceStorable TCB where
  makeObject := makeObjectTCB
  injectKO := KernelObject.KOTCB
  projectKO_opt | .KOTCB e => some e | _ => none

instance : PSpaceStorable UserData where
  makeObject := UserData.UserData
  injectKO := fun _ => KernelObject.KOUserData
  projectKO_opt | .KOUserData => some UserData.UserData | _ => none

instance : PSpaceStorable UserDataDevice where
  makeObject := UserDataDevice.UserDataDevice
  injectKO := fun _ => KernelObject.KOUserDataDevice
  projectKO_opt | .KOUserDataDevice => some UserDataDevice.UserDataDevice | _ => none

instance : PSpaceStorable PTE where
  makeObject := PTE.InvalidPTE
  injectKO := fun p => KernelObject.KOArch (ArchKernelObject.KOPTE p)
  projectKO_opt | .KOArch (.KOPTE p) => some p | _ => none

instance : PSpaceStorable ASIDPool where
  makeObject := makeObjectASIDPool
  injectKO := fun p => KernelObject.KOArch (ArchKernelObject.KOASIDPool p)
  projectKO_opt | .KOArch (.KOASIDPool p) => some p | _ => none

end Sel4Lean.Spec
