import Sel4Lean.Spec.Prelude
import Sel4Lean.Monad.VCG

/-!
# `PSpaceStorable`: typed access to the object heap (hand-written, W2/W3)

The Haskell spec's only user-defined type class (`Model/PSpace.lhs:56`) and its eight instances
(`Object/Instances.lhs`, `Object/Instances/RISCV64.hs`). It is translated by hand because it is a single
class, and because the Haskell version is polymorphic over `MonadFail m`, which Lean has no direct
counterpart for. The shape follows l4v's Isabelle `pspace_storable` class:
`projectKO_opt :: kernel_object ⇒ 'a option`, with failure in the nondeterministic monad.

This file has the class and the helpers that need no object sizes; it is imported by every generated
module. `objBits`, `loadObject`/`updateObject` and the eight instances need generated definitions
(`objBitsKO`, `newArchTCB`, …), so they live in `PSpaceInstances.lean`. hs2lean leaves all names
defined in either file to them (`full.py`: `PROVIDED`).
-/

namespace Sel4Lean.Spec
open Sel4Lean (NondetM)
open Sel4Lean.NondetM (valid)
open scoped Sel4Lean.NondetM
open Sel4Lean.Exec (Word PPtr)

/-! ## Object kinds (l4v: `kernel_object_type`, `koTypeOf`, `archTypeOf`) -/

/-- Isabelle `datatype arch_kernel_object_type` (design/skel/RISCV64/ArchStructures_H.thy). -/
inductive RISCV64.ArchKernelObjectType where
  | PTET
  | ASIDPoolT
  deriving DecidableEq, Inhabited

/-- Isabelle `archTypeOf`. -/
def RISCV64.archTypeOf : ArchKernelObject → RISCV64.ArchKernelObjectType
  | .KOPTE _ => .PTET
  | .KOASIDPool _ => .ASIDPoolT

/-- Isabelle `datatype kernel_object_type` (design/skel/PSpaceStorable_H.thy). -/
inductive KernelObjectType where
  | EndpointT
  | NotificationT
  | CTET
  | TCBT
  | UserDataT
  | UserDataDeviceT
  | KernelDataT
  | ArchT (t : RISCV64.ArchKernelObjectType)
  deriving DecidableEq, Inhabited

/-- Isabelle `koTypeOf`. -/
def koTypeOf : KernelObject → KernelObjectType
  | .KOEndpoint _ => .EndpointT
  | .KONotification _ => .NotificationT
  | .KOCTE _ => .CTET
  | .KOTCB _ => .TCBT
  | .KOUserData => .UserDataT
  | .KOUserDataDevice => .UserDataDeviceT
  | .KOKernelData => .KernelDataT
  | .KOArch e => .ArchT (RISCV64.archTypeOf e)

/-! ## The classes (l4v: `pre_storable`, `pspace_storable`)

The Haskell has one class, `PSpaceStorable` (Model/PSpace.lhs:56), polymorphic over `MonadFail m`. l4v
splits it in two and states its laws as class assumptions; so do we, as `Prop` fields every instance proves
(l4v proves them in ObjectInstances_H). `loadObject`/`updateObject` are methods: the CTE instance overrides
them to reach CTEs stored inside TCBs. -/

/-- Isabelle `class pre_storable`. -/
class PreStorable (a : Type) where
  injectKO : a → KernelObject
  projectKO_opt : KernelObject → Option a
  /-- Isabelle `koType :: 'a itself ⇒ kernel_object_type` -/
  koType : KernelObjectType
  /-- Isabelle `project_inject` -/
  project_inject : ∀ (ko : KernelObject) (v : a), projectKO_opt ko = some v ↔ injectKO v = ko
  /-- Isabelle `project_koType` -/
  project_koType : ∀ (ko : KernelObject), (∃ v : a, projectKO_opt ko = some v) ↔ koTypeOf ko = koType

/-- Isabelle `class pspace_storable = pre_storable + …` -/
class PSpaceStorable (a : Type) extends PreStorable a where
  makeObject : a
  loadObject : Word → Word → Option Word → KernelObject → Kernel a
  updateObject : a → KernelObject → Word → Word → Option Word → Kernel KernelObject
  /-- Isabelle `updateObject_type`: an update keeps the object's kind. -/
  updateObject_type : ∀ (v : a) (ko : KernelObject) (p p' : Word) (p'' : Option Word) (s s' : KernelState)
    (ko' : KernelObject), (updateObject v ko p p' p'' s).1 (ko', s') → koTypeOf ko' = koTypeOf ko

export PreStorable (injectKO projectKO_opt koType)
export PSpaceStorable (makeObject loadObject updateObject)

/-- Isabelle `projectKO e ≡ case projectKO_opt e of None ⇒ fail | Some k ⇒ return k`. -/
def projectKO {a σ : Type} [PreStorable a] (o : KernelObject) : NondetM σ a :=
  match projectKO_opt o with
  | some x => pure x
  | none => NondetM.fail

/-- A result of `projectKO`: the projection succeeded, and the state is unchanged. -/
theorem projectKO_result {a σ : Type} [PreStorable a] {o : KernelObject} {s t : σ} {v : a}
    (h : (projectKO o s).1 (v, t)) : projectKO_opt o = some v ∧ t = s := by
  unfold projectKO at h
  cases hx : (projectKO_opt o : Option a) <;> rw [hx] at h
  · exact h.elim
  · cases h; exact ⟨rfl, rfl⟩

theorem projectKO_wp {a σ : Type} [PreStorable a] (o : KernelObject) (Q : a → σ → Prop) :
    ⟪fun s => ∀ v, projectKO_opt o = some v → Q v s⟫ (projectKO o) ⟪Q⟫ := by
  intro s h r s' hr
  obtain ⟨hx, rfl⟩ := projectKO_result hr
  exact h _ hx

/-- Haskell `mask n` at word type (Machine/RegisterSet.lhs:174). -/
abbrev maskW (n : Nat) : Word := (1 <<< n) - 1

/-- Haskell `deleteRange` (Model/PSpace.lhs:229), as l4v replaces it (design/skel/PSpaceFuns_H.thy):
remove every key in the `2^bits`-aligned region at `ptr`. The Haskell version splits the map and
deletes `Data.Map.keys` of the middle part; over maps-as-functions the filter needs no key listing. -/
def deleteRange {α : Type} (m : Word → Option α) (ptr : Word) (bits : Nat) : Word → Option α :=
  fun x => if x &&& ~~~(maskW bits) = ptr then none else m x

/-- Haskell `alignError n = fail (…)` (Model/PSpace.lhs:308). -/
def alignError {α σ : Type} (_n : Nat) : NondetM σ α := NondetM.fail

/-- Haskell `typeError t o = fail (…)` (Model/PSpace.lhs:304). -/
def typeError {α σ : Type} (_t : String) (_o : KernelObject) : NondetM σ α := NondetM.fail

/-- Haskell `alignCheck x n = unless (x .&. mask n == 0) $ alignError n` (Model/PSpace.lhs:312). -/
def alignCheck {σ : Type} (x : Word) (n : Nat) : NondetM σ Unit :=
  if x &&& maskW n == 0 then pure () else NondetM.fail

/-- Isabelle `magnitudeCheck x y n ≡ case y of None ⇒ return () | Some z ⇒ when (z - x < 1 << n) fail`
(the Haskell's `sizeCheck`, Model/PSpace.lhs:315). -/
def magnitudeCheck {σ : Type} (x : Word) (y : Option Word) (n : Nat) : NondetM σ Unit :=
  match y with
  | none => pure ()
  | some z => if z - x < 1 <<< n then NondetM.fail else pure ()

/-- Haskell `sizeCheck`: l4v's `magnitudeCheck`. -/
abbrev sizeCheck {σ : Type} := @magnitudeCheck σ

/-! ## Machine operations

The Haskell `MachineMonad` is `ReaderT MachineData IO` (the simulator). l4v's Isabelle replaces it with
`machine_monad = (machine_state, 'a) nondet_monad` and lifts it with `do_machine_op` through
`ksMachineState`, a field the Haskell `KernelState` does not have. We follow Isabelle: `MachineState` is
l4v's record and `KernelState` gets `ksMachineState` (both generated, `full.py`).
-/

/-- Haskell `doMachineOp :: MachineMonad a -> Kernel a` (Model/StateData.lhs), as l4v's
(design/skel/KernelStateData_H.thy): run the machine operation on `ksMachineState`, keep any of its results. -/
def doMachineOp {α : Type} (mop : MachineMonad α) : Kernel α :=
  NondetM.bind (NondetM.gets KernelState.ksMachineState) fun ms =>
  NondetM.bind (NondetM.selectF (mop ms)) fun (r, ms') =>
  NondetM.bind (NondetM.modify fun ks => { ks with ksMachineState := ms' }) fun _ =>
  NondetM.ret r

/-- `doMachineOp` lifts a machine-level Hoare triple to the kernel (l4v `dmo_wp`-style). -/
theorem doMachineOp_wp {α : Type} {mop : MachineMonad α} {P : MachineState → Prop}
    {Q : α → MachineState → Prop} (h : ⟪P⟫ mop ⟪Q⟫) (R : α → KernelState → Prop) :
    ⟪fun s => P s.ksMachineState ∧
       ∀ r ms', Q r ms' → R r { s with ksMachineState := ms' }⟫ (doMachineOp mop) ⟪R⟫ := by
  intro s ⟨hP, hR⟩ r s' hr
  simp only [doMachineOp, NondetM.gets_eq, NondetM.modify_eq, NondetM.bind, NondetM.ret,
    NondetM.selectF, Prod.mk.injEq] at hr
  obtain ⟨_, _, ⟨rfl, rfl⟩, ⟨r', ms'⟩, _, ⟨hres, rfl⟩, hrest⟩ := hr
  obtain ⟨_, _, ⟨-, rfl⟩, rfl, rfl⟩ := hrest
  exact hR _ _ (h _ hP _ _ hres)

end Sel4Lean.Spec
