import Sel4Lean.Spec.PSpaceStorable
import Sel4Lean.Spec.Gen.Mod.Object_Structures
import Sel4Lean.Spec.Gen.Mod.Object_Structures_RISCV64
import Sel4Lean.Spec.Gen.Mod.Config

/-!
# `PSpaceStorable` instances and object sizes (hand-written, W3)

The eight instances (`Object/Instances.lhs`, `Object/Instances/RISCV64.hs`), `objBits`, and the default
methods `loadObject`/`updateObject`, over the **generated** `objBitsKO`, `nullMDBNode`, `newArchTCB`,
`asidLowBits` and `timeSlice`. (Until W3 these were opaque: this file was part of `PSpaceStorable.lean`,
which every generated module imports, so it could not import generated modules.)

hs2lean imports this file into every module whose Haskell imports include `Object.Structures` and `Config`
(`full.py`), the point from which the Haskell instances are in scope.
-/

namespace Sel4Lean.Spec
open Sel4Lean (NondetM)
open Sel4Lean.Exec (Word PPtr)
open Sel4Lean.Spec.M.Object_Structures (objBitsKO nullMDBNode)
open Sel4Lean.Spec.M.Object_Structures_RISCV64 (newArchTCB asidLowBits)

/-- Haskell `objBits a = objBitsKO (injectKO a)` (Model/PSpace.lhs). -/
def objBits {a : Type} [PSpaceStorable a] (x : a) : Nat := objBitsKO (injectKO x)

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

/-- Haskell `makeObject` for `TCB` (Object/Instances.lhs:125). -/
def makeObjectTCB : TCB where
  tcbCTable := makeObject
  tcbVTable := makeObject
  tcbReply := makeObject
  tcbCaller := makeObject
  tcbIPCBufferFrame := makeObject
  tcbDomain := BoundedH.minB
  tcbState := ThreadState.Inactive
  tcbMCP := BoundedH.minB
  tcbPriority := BoundedH.minB
  tcbQueued := false
  tcbFault := none
  tcbTimeSlice := Sel4Lean.Spec.M.Config.timeSlice
  tcbFaultHandler := CPtr.CPtr 0
  tcbIPCBuffer := VPtr.VPtr 0
  tcbBoundNotification := none
  tcbSchedPrev := none
  tcbSchedNext := none
  tcbFlags := 0
  tcbArch := newArchTCB

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

/-- Haskell `makeObject` for `ASIDPool` (Object/Instances/RISCV64.hs:27):
`ASIDPool $ funPartialArray (const Nothing) (0, bit asidLowBits - 1)`. -/
def makeObjectASIDPool : ASIDPool := ASIDPool.ASIDPool (funPartialArray (fun _ => none) (0, ⟨(1 <<< asidLowBits) - 1⟩))

instance : PSpaceStorable ASIDPool where
  makeObject := makeObjectASIDPool
  injectKO := fun p => KernelObject.KOArch (ArchKernelObject.KOASIDPool p)
  projectKO_opt | .KOArch (.KOASIDPool p) => some p | _ => none

end Sel4Lean.Spec
