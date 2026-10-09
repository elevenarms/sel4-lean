-- SPDX-License-Identifier: GPL-2.0-only (derived from seL4/l4v, https://github.com/seL4/l4v)
import Sel4Lean.Spec.PSpaceInstances
import Sel4Lean.Spec.Gen.Mod.Object_CNode
import Sel4Lean.Spec.Gen.Mod.Model_StateData
import Sel4Lean.Spec.Gen.Mod.Model_PSpace
import Sel4Lean.Spec.Gen.Mod.API_Types_RISCV64
import Sel4Lean.Spec.Gen.Mod.Machine_Hardware_RISCV64

/-!
# Intermediate object creation (hand-written, W3): l4v's `Intermediate_H.thy`, `ArchIntermediate_H.thy`

"Intermediate function bodies that were once in the Haskell spec, but are now no longer" (l4v): the
refinement proofs for retyping go C ↔ Haskell ↔ *old Haskell* ↔ abstract, and these are the old-Haskell
definitions of object and capability creation. They exist only in l4v's Isabelle; ported as written there
(Isabelle `machine_word` for addresses, wrapped into the typed capability fields).
-/

namespace Sel4Lean.Spec.Intermediate
open Sel4Lean (NondetM)
open Sel4Lean.Exec (Word PPtr)
open Sel4Lean.Spec.M.Object_CNode (insertNewCap)
open Sel4Lean.Spec.M.Object_Structures (objBitsKO)
open Sel4Lean.Spec.M.Model_StateData (curDomain)
open Sel4Lean.Spec.M.Model_PSpace (lookupAround2)
open Sel4Lean.Spec.M.API_Types_RISCV64 (toAPIType)
open Sel4Lean.Spec.M.Machine_Hardware_RISCV64 (ptTranslationBits ptBits)
noncomputable section

/-- Isabelle `upto_enum_step`-free `[0 .e. n - 1]` at word type (empty for n = 0). -/
def wordsBelow (n : Nat) : List Word := (List.range n).map (BitVec.ofNat 64)

/-- Isabelle `createObjects'`: place `numObjects` copies of `val` (each in a `2^(objBitsKO val + gSize)`
block) at `ptr`, after checking alignment and that nothing overlaps from below. -/
def createObjects' (ptr : Word) (numObjects : Nat) (val : KernelObject) (gSize : Nat) : Kernel Unit :=
  let oBits := objBitsKO val
  let gBits := oBits + gSize
  NondetM.bind (NondetM.unlessM (ptr &&& maskW gBits = 0) (alignError gBits)) fun _ =>
  NondetM.bind (NondetM.gets KernelState.ksPSpace) fun ps =>
  let «end» := ptr + BitVec.ofNat 64 ((numObjects <<< gBits) - 1)
  let (before, _) := lookupAround2 «end» ps.psMap
  NondetM.bind (match before with
    | none => NondetM.ret ()
    | some (x, _) => NondetM.assertM (x < ptr)) fun _ =>
  let addresses := (wordsBelow (numObjects <<< gSize)).map fun (n : Word) => ptr + (n <<< oBits)
  let map' := addresses.foldr (fun addr m a => if a = addr then some val else m a) ps.psMap
  NondetM.modify fun ks => { ks with ksPSpace := { ps with psMap := map' } }

/-- Isabelle `createObjects`: `createObjects'`, returning the object addresses. -/
def createObjects (ptr : Word) (numObjects : Nat) (val : KernelObject) (gSize : Nat) : Kernel (List Word) :=
  let gBits := objBitsKO val + gSize
  NondetM.bind (createObjects' ptr numObjects val gSize) fun _ =>
  NondetM.ret ((wordsBelow numObjects).map fun (n : Word) => ptr + (n <<< gBits))

/-- Isabelle `createNewFrameCaps` (ArchIntermediate_H, an abbreviation there). -/
def createNewFrameCaps (regionBase : Word) (numObjects : Nat) (dev : Bool) (gSize : Nat)
    (pSize : VMPageSize) : Kernel (List ArchCapability) :=
  let data := if dev then KernelObject.KOUserDataDevice else KernelObject.KOUserData
  NondetM.bind (createObjects regionBase numObjects data gSize) fun addrs =>
  NondetM.bind (NondetM.modify fun ks =>
      let pages := fun addr => if addr ∈ addrs then some pSize else ks.gsUserPages addr
      { ks with gsUserPages := pages }) fun _ =>
  NondetM.ret (addrs.map fun n => ArchCapability.FrameCap ⟨n⟩ VMRights.VMReadWrite pSize dev none)

/-- Isabelle `createNewTableCaps` (ArchIntermediate_H, an abbreviation there). -/
def createNewTableCaps {a : Type} [PreStorable a] (regionBase : Word) (numObjects : Nat) (tableBits : Nat)
    (objectProto : a) (cap : PPtr PTE → Option (ASID × VPtr) → ArchCapability)
    (initialiseMappings : List (PPtr PTE) → Kernel Unit) : Kernel (List ArchCapability) :=
  let tableSize := tableBits - objBits objectProto
  NondetM.bind (createObjects regionBase numObjects (injectKO objectProto) tableSize) fun addrs =>
  let pts : List (PPtr PTE) := addrs.map fun a => ⟨a⟩
  NondetM.bind (initialiseMappings pts) fun _ =>
  NondetM.ret (pts.map fun pt => cap pt none)

/-- Isabelle `Arch_createNewCaps` (ArchIntermediate_H). -/
def Arch_createNewCaps (t : ObjectType) (regionBase : Word) (numObjects : Nat) (_userSize : Nat) (dev : Bool) :
    Kernel (List ArchCapability) :=
  match t with
  | .APIObjectType _ => NondetM.fail
  | .SmallPageObject => createNewFrameCaps regionBase numObjects dev 0 .RISCVSmallPage
  | .LargePageObject => createNewFrameCaps regionBase numObjects dev ptTranslationBits .RISCVLargePage
  | .HugePageObject =>
      createNewFrameCaps regionBase numObjects dev (ptTranslationBits + ptTranslationBits) .RISCVHugePage
  | .PageTableObject =>
      createNewTableCaps regionBase numObjects ptBits (makeObject : PTE) ArchCapability.PageTableCap
        (fun _ => NondetM.ret ())

/-- Isabelle `createNewCaps` (Intermediate_H). -/
def createNewCaps (t : ObjectType) (regionBase : Word) (numObjects : Nat) (userSize : Nat) (dev : Bool) :
    Kernel (List Capability) :=
  match toAPIType t with
  | some .TCBObject =>
      NondetM.bind curDomain fun curdom =>
      NondetM.bind (createObjects regionBase numObjects
        (injectKO { (makeObject : TCB) with tcbDomain := curdom }) 0) fun addrs =>
      NondetM.ret (addrs.map fun addr => Capability.ThreadCap ⟨addr⟩)
  | some .EndpointObject =>
      NondetM.bind (createObjects regionBase numObjects (injectKO (makeObject : Endpoint)) 0) fun addrs =>
      NondetM.ret (addrs.map fun addr => Capability.EndpointCap ⟨addr⟩ 0 true true true true)
  | some .NotificationObject =>
      NondetM.bind (createObjects regionBase numObjects (injectKO (makeObject : Notification)) 0) fun addrs =>
      NondetM.ret (addrs.map fun addr => Capability.NotificationCap ⟨addr⟩ 0 true true)
  | some .CapTableObject =>
      NondetM.bind (createObjects regionBase numObjects (injectKO (makeObject : CTE)) userSize) fun addrs =>
      NondetM.bind (NondetM.modify fun ks =>
          let cnodes := fun addr => if addr ∈ addrs then some userSize else ks.gsCNodes addr
          { ks with gsCNodes := cnodes }) fun _ =>
      NondetM.ret (addrs.map fun addr => Capability.CNodeCap ⟨addr⟩ userSize 0 0)
  | some .Untyped =>
      NondetM.ret ((wordsBelow numObjects).map fun (n : Word) =>
        Capability.UntypedCap dev ⟨regionBase + n * BitVec.ofNat 64 (2 ^ userSize)⟩ userSize 0)
  | none =>
      NondetM.bind (Arch_createNewCaps t regionBase numObjects userSize dev) fun archCaps =>
      NondetM.ret (archCaps.map Capability.ArchObjectCap)

/-- Isabelle `insertNewCaps` (Intermediate_H): create the capabilities and insert them under `srcSlot`. -/
def insertNewCaps (newType : ObjectType) (srcSlot : Word) (destSlots : List Word) (regionBase : Word)
    (magnitudeBits : Nat) (dev : Bool) : Kernel Unit :=
  NondetM.bind (createNewCaps newType regionBase destSlots.length magnitudeBits dev) fun caps =>
  NondetM.mapM_x (fun (slot, cap) => insertNewCap ⟨srcSlot⟩ ⟨slot⟩ cap) (destSlots.zip caps)

end
end Sel4Lean.Spec.Intermediate
