import Sel4Lean.Spec.PSpaceInstances
import Sel4Lean.Spec.Gen.Mod.Object_CNode
import Sel4Lean.Spec.Gen.Mod.Model_Failures

/-!
# Definitions that exist only in l4v's Isabelle design spec (hand-written, W3)

Small pieces of l4v's skeletons with no Haskell counterpart: `Delete_H.thy` (`slotsPointed`, `sethelper`, and
`finaliseSlot'`/`cteDeleteOne'`, the termination-friendly versions of the same Haskell bodies),
`FaultMonad_H.thy` (`nothingOnFailure`), `State_H.thy` (`fromPPtr`), `PSpaceStruct_H.thy` (`ptrBits`),
`Platform.thy` (`irq_len`), and `API_H.thy`'s unspecified kernel assertions.
-/

namespace Sel4Lean.Spec.DesignOnly
open Sel4Lean (NondetM)
open Sel4Lean.Exec (Word PPtr)
noncomputable section

/-- Isabelle `nothingOnFailure m ≡ m <catch> (λx. return Nothing)` (FaultMonad_H). -/
def nothingOnFailure {f a : Type} [Inhabited f] [Inhabited a] (m : KernelF f (Option a)) : Kernel (Option a) :=
  Sel4Lean.Spec.M.Model_Failures.catchFailure m (fun _ => pure none)

/-- Isabelle `slotsPointed` (Delete_H): the slots a CNode, thread or zombie capability points to. -/
def slotsPointed : Capability → Word → Prop
  | .CNodeCap ptr _ _ _ => fun x => x = ptr.ptr
  | .ThreadCap ptr => fun x => x = ptr.ptr
  | .Zombie ptr _ _ => fun x => x = ptr.ptr
  | _ => fun _ => False

/-- Isabelle `sethelper` (Delete_H). -/
def sethelper {α : Type} : Bool → (α → Prop) → α → Prop
  | true, _ => fun _ => False
  | false, s => s

/-- Isabelle `finaliseSlot'` (Delete_H): the `function`-package version of `finaliseSlot`, with the same
Haskell bodies (`finaliseSlot ≡ finaliseSlot'`); its termination is proved in Refine (TODO(W4)). -/
abbrev finaliseSlot' := @Sel4Lean.Spec.M.Object_CNode.finaliseSlot
/-- Isabelle `cteDeleteOne'` (Delete_H): `cteDeleteOne ≡ cteDeleteOne'`. -/
abbrev cteDeleteOne' := @Sel4Lean.Spec.M.Object_CNode.cteDeleteOne

/-- Isabelle `fromPPtr` (State_H): pointers are machine words. -/
abbrev fromPPtr {a : Type} (p : PPtr a) : Word := p.ptr

/-- Isabelle `ptrBits ≡ to_bl`: a word as its list of bits, most significant first. -/
def ptrBits (w : Word) : List Bool := (List.range 64).reverse.map fun i => w.getLsbD i

/-- Isabelle `value_type irq_len = Kernel_Config.irqBits`. -/
abbrev irq_len : Nat := KernelConfig.irqBits

/-- Isabelle `kernelExitAssertions` (API_H): declared without the Haskell body ("replaced by actual
assertions in the proofs"), so unspecified. -/
opaque kernelExitAssertions : KernelState → Bool
/-- Isabelle `fastpathKernelAssertions` (API_H): unspecified, as above. -/
opaque fastpathKernelAssertions : KernelState → Bool

/-- Isabelle `Types_H.init_data`: l4v keeps the Haskell `InitData` record as a type of its own (with
`initVPtrOffset`), next to the `KernelInitMonad_H` record the spec uses (`Sel4Lean.Spec.InitData`). -/
structure HaskellInitData where
  initFreeMemory : List Region
  initSlotPosCur : Word
  initSlotPosMax : Word
  initBootInfo : BIFrameData
  initVPtrOffset : VPtr
  initBootInfoFrame : PAddr

end
end Sel4Lean.Spec.DesignOnly

namespace Sel4Lean.Spec.DesignOnly.State_H
/-- Isabelle `PPtr` (State_H): the identity on machine words; Lean keeps the pointee type. -/
abbrev PPtr {a : Type} (w : Sel4Lean.Exec.Word) : Sel4Lean.Exec.PPtr a := ⟨w⟩
end Sel4Lean.Spec.DesignOnly.State_H
