-- SPDX-License-Identifier: GPL-2.0-only (derived from seL4/l4v, https://github.com/seL4/l4v)
import Sel4Lean.Spec.PSpaceStorable
import Sel4Lean.Spec.Gen.Mod.Object_Structures
import Sel4Lean.Spec.Gen.Mod.Object_Structures_RISCV64
import Sel4Lean.Spec.Gen.Mod.Config
import Sel4Lean.Tactic.WP

/-!
# `PSpaceStorable` instances (hand-written, W3): l4v's `PSpaceStorable_H` and `ObjectInstances_H`

`objBits`, the default methods `loadObject_default`/`updateObject_default`, and the eight instances, over
the generated `objBitsKO`, `nullMDBNode`, `newArchTCB`, `asidLowBits` and `timeSlice`. Every instance
proves l4v's class laws (`project_inject`, `project_koType`, `updateObject_type`).

The CTE instance overrides `loadObject`/`updateObject` (Object/Instances.lhs; l4v `loadObject_cte`,
`updateObject_cte`): the five capability slots of a TCB are CTEs stored *inside* the TCB object, and
`getObject`/`setObject` on a CTE pointer into a TCB must reach them. (Before W3's Isabelle cross-check
the Lean port gave CTEs the default methods, which fail on those pointers.)

hs2lean imports this file into every module whose Haskell imports reach `Object.Structures` and `Config`.
-/

namespace Sel4Lean.Spec
open Sel4Lean (NondetM)
open Sel4Lean.NondetM (valid)
open scoped Sel4Lean.NondetM
open Sel4Lean.Exec (Word PPtr)
open Sel4Lean.Spec.M.Object_Structures (objBitsKO nullMDBNode tcbVTableSlot tcbCTableSlot tcbReplySlot
  tcbCallerSlot tcbIPCBufferSlot)
open Sel4Lean.Spec.M.Object_Structures_RISCV64 (newArchTCB asidLowBits)

/-- Isabelle `objBits v ≡ objBitsKO (injectKO v)`. -/
def objBits {a : Type} [PreStorable a] (v : a) : Nat := objBitsKO (injectKO v)

/-- Isabelle `loadObject_default`. -/
def loadObject_default {a : Type} [PreStorable a] (ptr ptr' : Word) (next : Option Word)
    (obj : KernelObject) : Kernel a :=
  NondetM.bind (NondetM.assertM (ptr = ptr')) fun _ =>
  NondetM.bind (projectKO obj) fun val =>
  NondetM.bind (alignCheck ptr (objBits val)) fun _ =>
  NondetM.bind (magnitudeCheck ptr next (objBits val)) fun _ =>
  NondetM.ret val

/-- Isabelle `updateObject_default`. -/
def updateObject_default {a : Type} [PreStorable a] (val : a) (oldObj : KernelObject) (ptr ptr' : Word)
    (next : Option Word) : Kernel KernelObject :=
  NondetM.bind (NondetM.assertM (ptr = ptr')) fun _ =>
  NondetM.bind (projectKO (a := a) oldObj) fun _ =>
  NondetM.bind (alignCheck ptr (objBits val)) fun _ =>
  NondetM.bind (magnitudeCheck ptr next (objBits val)) fun _ =>
  NondetM.ret (injectKO val)

theorem koTypeOf_injectKO {a : Type} [PreStorable a] (v : a) :
    koTypeOf (injectKO v) = PreStorable.koType a :=
  (PreStorable.project_koType _).1 ⟨v, (PreStorable.project_inject _ _).2 rfl⟩

theorem koTypeOf_of_project {a : Type} [PreStorable a] {ko : KernelObject} {v : a}
    (h : projectKO_opt ko = some v) : koTypeOf ko = PreStorable.koType a :=
  (PreStorable.project_koType _).1 ⟨v, h⟩

theorem updateObject_default_type {a : Type} [PreStorable a] (v : a) (ko : KernelObject) (p p' : Word)
    (p'' : Option Word) (s s' : KernelState) (ko' : KernelObject)
    (h : (updateObject_default v ko p p' p'' s).1 (ko', s')) : koTypeOf ko' = koTypeOf ko := by
  obtain ⟨_, _, -, _, _, hp, _, _, -, _, _, -, hr⟩ := h
  cases hr
  rw [koTypeOf_injectKO, koTypeOf_of_project (projectKO_result hp).1]

instance : PreStorable Endpoint where
  injectKO := KernelObject.KOEndpoint
  projectKO_opt | .KOEndpoint e => some e | _ => none
  koType := .EndpointT
  project_inject := by intro ko v; cases ko <;> simp [eq_comm]
  project_koType := by intro ko; cases ko <;> simp [koTypeOf]

instance : PreStorable Notification where
  injectKO := KernelObject.KONotification
  projectKO_opt | .KONotification e => some e | _ => none
  koType := .NotificationT
  project_inject := by intro ko v; cases ko <;> simp [eq_comm]
  project_koType := by intro ko; cases ko <;> simp [koTypeOf]

instance : PreStorable CTE where
  injectKO := KernelObject.KOCTE
  projectKO_opt | .KOCTE e => some e | _ => none
  koType := .CTET
  project_inject := by intro ko v; cases ko <;> simp [eq_comm]
  project_koType := by intro ko; cases ko <;> simp [koTypeOf]

instance : PreStorable TCB where
  injectKO := KernelObject.KOTCB
  projectKO_opt | .KOTCB e => some e | _ => none
  koType := .TCBT
  project_inject := by intro ko v; cases ko <;> simp [eq_comm]
  project_koType := by intro ko; cases ko <;> simp [koTypeOf]

instance : PreStorable UserData where
  injectKO := fun _ => KernelObject.KOUserData
  projectKO_opt | .KOUserData => some UserData.UserData | _ => none
  koType := .UserDataT
  project_inject := by intro ko v; cases v; cases ko <;> simp
  project_koType := by intro ko; cases ko <;> simp [koTypeOf]

instance : PreStorable UserDataDevice where
  injectKO := fun _ => KernelObject.KOUserDataDevice
  projectKO_opt | .KOUserDataDevice => some UserDataDevice.UserDataDevice | _ => none
  koType := .UserDataDeviceT
  project_inject := by intro ko v; cases v; cases ko <;> simp
  project_koType := by intro ko; cases ko <;> simp [koTypeOf]

instance : PreStorable PTE where
  injectKO := fun p => KernelObject.KOArch (ArchKernelObject.KOPTE p)
  projectKO_opt | .KOArch (.KOPTE p) => some p | _ => none
  koType := .ArchT .PTET
  project_inject := by
    intro ko v; cases ko <;> simp
    next a => cases a <;> simp [eq_comm]
  project_koType := by
    intro ko; cases ko <;> simp [koTypeOf]
    next a => cases a <;> simp [RISCV64.archTypeOf]

instance : PreStorable ASIDPool where
  injectKO := fun p => KernelObject.KOArch (ArchKernelObject.KOASIDPool p)
  projectKO_opt | .KOArch (.KOASIDPool p) => some p | _ => none
  koType := .ArchT .ASIDPoolT
  project_inject := by
    intro ko v; cases ko <;> simp
    next a => cases a <;> simp [eq_comm]
  project_koType := by
    intro ko; cases ko <;> simp [koTypeOf]
    next a => cases a <;> simp [RISCV64.archTypeOf]

/-! ## `pspace_storable` instances -/

instance : PSpaceStorable Endpoint where
  makeObject := Endpoint.IdleEP
  loadObject := loadObject_default
  updateObject := updateObject_default
  updateObject_type := updateObject_default_type

instance : PSpaceStorable Notification where
  makeObject := Notification.NTFN NTFN.IdleNtfn none
  loadObject := loadObject_default
  updateObject := updateObject_default
  updateObject_type := updateObject_default_type

/-- Isabelle `makeObject_tcb` (Object/Instances.lhs:125). -/
def makeObjectTCB : TCB where
  tcbCTable := CTE.CTE Capability.NullCap nullMDBNode
  tcbVTable := CTE.CTE Capability.NullCap nullMDBNode
  tcbReply := CTE.CTE Capability.NullCap nullMDBNode
  tcbCaller := CTE.CTE Capability.NullCap nullMDBNode
  tcbIPCBufferFrame := CTE.CTE Capability.NullCap nullMDBNode
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
  loadObject := loadObject_default
  updateObject := updateObject_default
  updateObject_type := updateObject_default_type

/-- CTE slots inside a TCB: `slot << objBits (undefined :: cte)` (Isabelle `toOffset`). -/
def cteOffset (slot : Word) : Word := slot <<< objBits (undefinedH : CTE)

/-- Isabelle `loadObject_cte` (ObjectInstances_H): a CTE stands alone (`KOCTE`) or is one of the five
slots of a TCB, found by its offset from the TCB's address `ptr'`. -/
def loadObject_cte (ptr ptr' : Word) (next : Option Word) (obj : KernelObject) : Kernel CTE :=
  match obj with
  | .KOCTE cte =>
      NondetM.bind (NondetM.unlessM (ptr = ptr') NondetM.fail) fun _ =>
      NondetM.bind (alignCheck ptr (objBits cte)) fun _ =>
      NondetM.bind (magnitudeCheck ptr next (objBits cte)) fun _ =>
      NondetM.ret cte
  | .KOTCB tcb =>
      NondetM.bind (alignCheck ptr' (objBits tcb)) fun _ =>
      NondetM.bind (magnitudeCheck ptr' next (objBits tcb)) fun _ =>
      let x := ptr - ptr'
      if x = cteOffset tcbVTableSlot then NondetM.ret tcb.tcbVTable
      else if x = cteOffset tcbCTableSlot then NondetM.ret tcb.tcbCTable
      else if x = cteOffset tcbReplySlot then NondetM.ret tcb.tcbReply
      else if x = cteOffset tcbCallerSlot then NondetM.ret tcb.tcbCaller
      else if x = cteOffset tcbIPCBufferSlot then NondetM.ret tcb.tcbIPCBufferFrame
      else NondetM.fail
  | _ => typeError "CTE" obj

/-- Isabelle `updateObject_cte` (ObjectInstances_H): write a standalone CTE, or the TCB slot it names. -/
def updateObject_cte (cte : CTE) (oldObj : KernelObject) (ptr ptr' : Word) (next : Option Word) :
    Kernel KernelObject :=
  match oldObj with
  | .KOCTE _ =>
      NondetM.bind (NondetM.unlessM (ptr = ptr') NondetM.fail) fun _ =>
      NondetM.bind (alignCheck ptr (objBits cte)) fun _ =>
      NondetM.bind (magnitudeCheck ptr next (objBits cte)) fun _ =>
      NondetM.ret (KernelObject.KOCTE cte)
  | .KOTCB tcb =>
      NondetM.bind (alignCheck ptr' (objBits tcb)) fun _ =>
      NondetM.bind (magnitudeCheck ptr' next (objBits tcb)) fun _ =>
      let x := ptr - ptr'
      if x = cteOffset tcbVTableSlot then NondetM.ret (.KOTCB { tcb with tcbVTable := cte })
      else if x = cteOffset tcbCTableSlot then NondetM.ret (.KOTCB { tcb with tcbCTable := cte })
      else if x = cteOffset tcbReplySlot then NondetM.ret (.KOTCB { tcb with tcbReply := cte })
      else if x = cteOffset tcbCallerSlot then NondetM.ret (.KOTCB { tcb with tcbCaller := cte })
      else if x = cteOffset tcbIPCBufferSlot then NondetM.ret (.KOTCB { tcb with tcbIPCBufferFrame := cte })
      else NondetM.fail
  | _ => typeError "CTE" oldObj

theorem updateObject_cte_type (v : CTE) (ko : KernelObject) (p p' : Word) (p'' : Option Word)
    (s s' : KernelState) (ko' : KernelObject) (h : (updateObject_cte v ko p p' p'' s).1 (ko', s')) :
    koTypeOf ko' = koTypeOf ko := by
  cases ko with
  | KOCTE c =>
    obtain ⟨_, _, -, _, _, -, _, _, -, hr⟩ := h
    cases hr; rfl
  | KOTCB t =>
    obtain ⟨_, _, -, _, _, -, hr⟩ := h
    dsimp only at hr
    repeat' (split at hr)
    all_goals first | (cases hr; rfl) | exact hr.elim
  | _ => exact h.elim

instance : PSpaceStorable CTE where
  makeObject := CTE.CTE Capability.NullCap nullMDBNode
  loadObject := loadObject_cte
  updateObject := updateObject_cte
  updateObject_type := updateObject_cte_type

instance : PSpaceStorable UserData where
  makeObject := UserData.UserData
  loadObject := loadObject_default
  updateObject := updateObject_default
  updateObject_type := updateObject_default_type

instance : PSpaceStorable UserDataDevice where
  makeObject := UserDataDevice.UserDataDevice
  loadObject := loadObject_default
  updateObject := updateObject_default
  updateObject_type := updateObject_default_type

instance : PSpaceStorable PTE where
  makeObject := PTE.InvalidPTE
  loadObject := loadObject_default
  updateObject := updateObject_default
  updateObject_type := updateObject_default_type

/-- Isabelle `makeObject_asidpool`: `ASIDPool $ funPartialArray (const Nothing) (0, bit asidLowBits - 1)`. -/
def makeObjectASIDPool : ASIDPool :=
  ASIDPool.ASIDPool (funPartialArray (fun _ => none) (0, ⟨(1 <<< asidLowBits) - 1⟩))

instance : PSpaceStorable ASIDPool where
  makeObject := makeObjectASIDPool
  loadObject := loadObject_default
  updateObject := updateObject_default
  updateObject_type := updateObject_default_type

end Sel4Lean.Spec
