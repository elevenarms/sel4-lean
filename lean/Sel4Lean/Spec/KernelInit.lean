-- SPDX-License-Identifier: GPL-2.0-only (derived from seL4/l4v, https://github.com/seL4/l4v)
import Sel4Lean.Spec.PSpaceStorable
import Sel4Lean.Spec.Gen.Mod.Model_PSpace
import Sel4Lean.Spec.Gen.Mod.Model_StateData_RISCV64
import Sel4Lean.Spec.Gen.Mod.Object_Structures
import Sel4Lean.Spec.Gen.Mod.Machine_Hardware_RISCV64

/-!
# Kernel initialisation monad (hand-written, W3): l4v's `KernelInitMonad_H.thy` and `KernelInit_H.thy`

l4v does not take the Haskell's init plumbing (`Init.lhs`: `NOT … InitData doKernelOp runInit
noInitFailure coverOf …`) or anything from `BootInfo.lhs`; it defines them in the design skeletons:

* the kernel state lives *inside* the init record (`init_data.initKernelState`, generated into
  `Gen/Types.lean`), and `doKernelOp` runs a kernel operation on it with `select_f`, like `doMachineOp`;
* the bootinfo capability numbers (`biCapNull` …), `itASID`, `biFrameSizeBits` and `nopBIFrameData` are
  unspecified `consts` (Lean `opaque`), not the Haskell `BootInfo.lhs` values;
* `runInit` always fails: l4v specifies the initialisation steps, not a run of them;
* `newKernelState` is l4v's record (with the ghost `gsMaxObjectSize = card UNIV`).

hs2lean aliases the Haskell names to these (`full.py`: `L4V_OVERRIDES`).
-/

namespace Sel4Lean.Spec.KernelInit
open Sel4Lean (NondetM)
open Sel4Lean.Exec (Word PPtr)

/-- Isabelle `noInitFailure ≡ liftE`. -/
def noInitFailure {α : Type} (m : KernelInitState α) : KernelInit α := ExceptT.lift m

/-- Isabelle `doKernelOp`: run a kernel operation on `initKernelState` and keep any of its results. -/
def doKernelOp {α : Type} (kop : Kernel α) : KernelInit α :=
  ExceptT.mk <|
  NondetM.bind (NondetM.gets InitData.initKernelState) fun ks =>
  NondetM.bind (NondetM.selectF (kop ks)) fun (r, ks') =>
  NondetM.bind (NondetM.modify fun d => { d with initKernelState := ks' }) fun _ =>
  NondetM.ret (Except.ok r)

/-! ## Unspecified constants (Isabelle `consts`) -/

opaque itASID : ASID
opaque biCapNull : Word
opaque biCapITTCB : Word
opaque biCapITCNode : Word
opaque biCapITPD : Word
opaque biCapIRQControl : Word
opaque biCapASIDControl : Word
opaque biCapITASIDPool : Word
opaque biCapIOPort : Word
opaque biCapIOSpace : Word
opaque biCapBIFrame : Word
opaque biCapITIPCBuf : Word
opaque biCapDynStart : Word
opaque biFrameSizeBits : Nat
opaque nopBIFrameData : BIFrameData

/-- Isabelle `runInit` (KernelInitMonad_H): set up the init record around the current kernel state, run
the initialisation, and fail either way. -/
def runInit {α β : Type} (_initOffset : VPtr) (doInit : KernelInit α) : Kernel β :=
  NondetM.bind NondetM.get fun ks =>
  let initData : InitData :=
    { initFreeMemory := [], initSlotPosCur := 0, initSlotPosMax := 1 <<< Sel4Lean.Spec.M.Machine_Hardware_RISCV64.pageBits,
      initBootInfo := nopBIFrameData, initBootInfoFrame := PAddr.PAddr 0, initKernelState := ks }
  NondetM.bind (NondetM.selectF (doInit.run initData)) fun _ => NondetM.fail

/-! ## `KernelInit_H.thy` -/

/-- Isabelle `coverOf`: the smallest region covering a list of regions. -/
def coverOf : List Region → Region
  | [] => Region.Region (⟨0⟩, ⟨0⟩)
  | [x] => x
  | x :: xs =>
    let (l, h) := x.fromRegion
    let (ll, hh) := (coverOf xs).fromRegion
    let ln := if l.ptr ≤ ll.ptr then l else ll
    let hn := if h.ptr ≤ hh.ptr then hh else h
    Region.Region (ln, hn)

/-- Isabelle `syncBIFrame ≡ returnOk ()`. -/
def syncBIFrame : KernelInit Unit := pure ()

opaque newKSDomSchedule : List (Domain × Ticks)
opaque newKSDomScheduleIdx : Nat
opaque newKSCurDomain : Domain
opaque newKSDomainTime : Ticks

/-- Isabelle `newKernelState` (KernelInit_H). -/
noncomputable def newKernelState (data_start : Word) : KernelState where
  ksPSpace := Sel4Lean.Spec.M.Model_PSpace.newPSpace
  gsUserPages := fun _ => none
  gsCNodes := fun _ => none
  gsUntypedZeroRanges := fun _ => False
  gsMaxObjectSize := 2 ^ 64        -- card (UNIV :: machine_word set)
  ksDomScheduleIdx := newKSDomScheduleIdx
  ksDomScheduleStart := 0
  ksDomSchedule := newKSDomSchedule
  ksCurDomain := newKSCurDomain
  ksDomainTime := newKSDomainTime
  ksReadyQueues := fun _ => Sel4Lean.Spec.M.Object_Structures.emptyQueue
  ksReadyQueuesL1Bitmap := fun _ => 0
  ksReadyQueuesL2Bitmap := fun _ => 0
  ksCurThread := undefinedH
  ksIdleThread := undefinedH
  ksSchedulerAction := SchedulerAction.ResumeCurrentThread
  ksInterruptState := undefinedH
  ksWorkUnitsCompleted := 0
  ksArchState := (Sel4Lean.Spec.M.Model_StateData_RISCV64.newKernelState (PAddr.PAddr data_start)).1
  ksMachineState := init_machine_state

end Sel4Lean.Spec.KernelInit
