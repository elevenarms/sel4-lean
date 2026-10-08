import Sel4Lean.Spec.PSpaceStorable
import Sel4Lean.Spec.Gen.Mod.Machine_Hardware_RISCV64_HiFive

/-!
# Machine operations (hand-written, W3)

The Haskell model implements these in `Machine/Hardware/RISCV64.hs` by calling the simulator
(`ask` the callback pointer, `liftIO`). l4v's Isabelle replaces them with definitions over
`machine_state` (spec/machine/RISCV64/MachineOps.thy, spec/machine/MachineMonad.thy); this file
ports those. hs2lean aliases the RISCV64 module's operations to these (`full.py`: `MACHINE_OPS`).

Isabelle `consts'` (unspecified constants) are Lean `opaque`s. The one `axiomatization`, the IRQ
oracle's bound, becomes an opaque value of a subtype, so the bound is a theorem and no axiom is added.
Operations l4v does not model (`getDeviceRegions`, `getKernelDevices`, `initIRQController`: boot code)
stay opaque stubs in the generated module.
-/

namespace Sel4Lean.Spec.MachineOps
open Sel4Lean (NondetM)
open Sel4Lean.Exec (Word PPtr)
open Sel4Lean.Spec.M.Machine_Hardware_RISCV64_HiFive (irqInvalid)

/-! ## Lifting (MachineMonad.thy) -/

/-- Isabelle `'a machine_rest_monad`. -/
abbrev MachineRestMonad (α : Type) := NondetM MachineStateRest α

/-- Isabelle `machine_rest_lift`: run an operation on the unspecified rest of the machine. -/
def machineRestLift {α : Type} (f : MachineRestMonad α) : MachineMonad α :=
  NondetM.bind (NondetM.gets MachineState.machine_state_rest) fun mr =>
  NondetM.bind (NondetM.selectF (f mr)) fun (r, mr') =>
  NondetM.bind (NondetM.modify fun s => { s with machine_state_rest := mr' }) fun _ =>
  NondetM.ret r

/-- Isabelle `ignore_failure f ≡ λs. if fst (f s) = {} then ({((),s)}, False) else (fst (f s), False)`. -/
def ignoreFailure {σ : Type} (f : NondetM σ Unit) : NondetM σ Unit := fun s =>
  (fun p => (f s).1 p ∨ ((¬ ∃ q, (f s).1 q) ∧ p = ((), s)), False)

/-- Isabelle `machine_op_lift ≡ machine_rest_lift o ignore_failure`. -/
def machineOpLift (f : MachineRestMonad Unit) : MachineMonad Unit :=
  machineRestLift (ignoreFailure f)

/-- Isabelle `upto_enum_step a b c` (`[a, b .e. c]`) at word type. -/
def wordStepList (a b c : Word) : List Word :=
  if c < a then [] else (List.range ((c - a) / (b - a)).toNat.succ).map fun i => a + (BitVec.ofNat 64 i) * (b - a)

/-! ## Memory -/

/-- Isabelle `loadWord`: eight bytes of `underlying_memory`, little-endian (`word_rcat` of
`m (p + 7) … m p`), at an 8-byte-aligned address. -/
def loadWord (p : PPtr Word) : MachineMonad Word :=
  NondetM.bind (NondetM.gets MachineState.underlying_memory) fun m =>
  NondetM.bind (NondetM.assertM (p.ptr &&& 7 = 0)) fun _ =>
  NondetM.ret ((List.range 8).foldl (fun w i => w ||| ((m (p.ptr + BitVec.ofNat 64 i)).zeroExtend 64 <<< (8 * i))) 0)

/-- Isabelle `storeWord`: byte `i` of `w` (little-endian) to `p + i`. -/
def storeWord (p : PPtr Word) (w : Word) : MachineMonad Unit :=
  NondetM.bind (NondetM.assertM (p.ptr &&& 7 = 0)) fun _ =>
  NondetM.modify fun s =>
    let mem := (List.range 8).foldl
      (fun m i a => if a = p.ptr + BitVec.ofNat 64 i then (w >>> (8 * i)).truncate 8 else m a) s.underlying_memory
    { s with underlying_memory := mem }

/-- Isabelle `consts' memory_regions`. -/
opaque memoryRegions : List (PAddr × PAddr)

/-- Isabelle `getMemoryRegions ≡ return memory_regions`. -/
def getMemoryRegions : MachineMonad (List (PAddr × PAddr)) := NondetM.ret memoryRegions

/-- Isabelle `storeWordVM ≡ return ()` (simulator only). -/
def storeWordVM (_p : PPtr Word) (_w : Word) : MachineMonad Unit := NondetM.ret ()

/-! ## Timer -/

opaque configureTimer_impl : MachineRestMonad Unit
opaque configureTimer_val : MachineState → RISCV64.IRQ
opaque initTimer_impl : MachineRestMonad Unit
opaque resetTimer_impl : MachineRestMonad Unit

def configureTimer : MachineMonad RISCV64.IRQ :=
  NondetM.bind (machineOpLift configureTimer_impl) fun _ => NondetM.gets configureTimer_val

def initTimer : MachineMonad Unit := machineOpLift initTimer_impl

def resetTimer : MachineMonad Unit := machineOpLift resetTimer_impl

/-! ## Debug -/

/-- Isabelle `debugPrint ≡ λmessage. return ()`. -/
def debugPrint (_msg : String) : MachineMonad Unit := NondetM.ret ()

/-! ## Interrupt controller -/

opaque setIRQTrigger_impl : RISCV64.IRQ → Bool → MachineRestMonad Unit
opaque plic_complete_claim_impl : RISCV64.IRQ → MachineRestMonad Unit

def setIRQTrigger (irq : RISCV64.IRQ) (trigger : Bool) : MachineMonad Unit :=
  machineOpLift (setIRQTrigger_impl irq trigger)

def plic_complete_claim (irq : RISCV64.IRQ) : MachineMonad Unit :=
  machineOpLift (plic_complete_claim_impl irq)

/-- Isabelle `non_kernel_IRQs = {}` on RISCV64. -/
def nonKernelIRQs (_irq : RISCV64.IRQ) : Prop := False

/-- Isabelle `maxIRQ` for HiFive (`maxBound = IRQ 54`, Hardware/RISCV64/HiFive.hs). -/
def maxIRQ : RISCV64.IRQ := ⟨54⟩

/-- Isabelle `axiomatization irq_oracle :: nat ⇒ irq where irq_oracle_max_irq: ∀n. irq_oracle n ≤ maxIRQ`,
as an opaque inhabitant of the subtype: the bound is a theorem, not an axiom. -/
opaque irqOracleImpl : {f : Nat → RISCV64.IRQ // ∀ n, f n ≤ maxIRQ} :=
  ⟨fun _ => ⟨0⟩, fun _ => by show (0 : BitVec 32) ≤ 54; decide⟩

def irqOracle : Nat → RISCV64.IRQ := irqOracleImpl.val

theorem irqOracle_max_irq (n : Nat) : irqOracle n ≤ maxIRQ := irqOracleImpl.property n

/-- Isabelle `getActiveIRQ`: oracle-based and deterministic (for information-flow proofs). It advances
`irq_state`, then reports the oracle's IRQ unless it is masked or invalid. -/
def getActiveIRQ (_inKernel : Bool) : MachineMonad (Option RISCV64.IRQ) :=
  NondetM.bind (NondetM.gets MachineState.irq_masks) fun isMasked =>
  NondetM.bind (NondetM.modify fun s => { s with irq_state := s.irq_state + 1 }) fun _ =>
  NondetM.bind (NondetM.gets fun s => irqOracle s.irq_state) fun active =>
  -- `non_kernel_IRQs` is empty on RISCV64, so the `in_kernel ∧ …` disjunct is always false
  if isMasked active ∨ active = irqInvalid then NondetM.ret none else NondetM.ret (some active)

/-- Isabelle `maskInterrupt m irq ≡ modify (λs. s⦇irq_masks := (irq_masks s)(irq := m)⦈)`. -/
def maskInterrupt (m : Bool) (irq : RISCV64.IRQ) : MachineMonad Unit :=
  NondetM.modify fun s => { s with irq_masks := fun i => if i = irq then m else s.irq_masks i }

/-- Isabelle `ackInterrupt ≡ λirq. return ()`. -/
def ackInterrupt (_irq : RISCV64.IRQ) : MachineMonad Unit := NondetM.ret ()

/-- Isabelle `setInterruptMode ≡ λirq levelTrigger polarityLow. return ()`. -/
def setInterruptMode (_irq : RISCV64.IRQ) (_level _polarityLow : Bool) : MachineMonad Unit := NondetM.ret ()

/-! ## Clearing memory -/

/-- Isabelle `clearMemory ptr len ≡ mapM_x (λp. storeWord p 0) [ptr, ptr + word_size .e. ptr + len - 1]`. -/
def clearMemory (ptr : PPtr Word) (bytelength : Nat) : MachineMonad Unit :=
  NondetM.mapM_x (fun p => storeWord ⟨p⟩ 0)
    (wordStepList ptr.ptr (ptr.ptr + 8) (ptr.ptr + BitVec.ofNat 64 bytelength - 1))

/-- Isabelle `clearMemoryVM ≡ return ()` (simulator only). -/
def clearMemoryVM (_ptr : PPtr Word) (_bits : Nat) : MachineMonad Unit := NondetM.ret ()

/-- Isabelle `initMemory == clearMemory`. -/
abbrev initMemory := clearMemory

/-- Isabelle `freeMemory ptr bits ≡ mapM_x (λp. storeWord p 0) [ptr, ptr + word_size .e. ptr + 2 ^ bits - 1]`. -/
def freeMemory (ptr : PPtr Word) (bits : Nat) : MachineMonad Unit :=
  NondetM.mapM_x (fun p => storeWord ⟨p⟩ 0)
    (wordStepList ptr.ptr (ptr.ptr + 8) (ptr.ptr + (1 <<< bits) - 1))

/-! ## Caches, barriers, faults, virtual memory -/

opaque initL2Cache_impl : MachineRestMonad Unit
opaque hwASIDFlush_impl : Word → MachineRestMonad Unit
opaque sfence_impl : MachineRestMonad Unit
opaque stval_val : MachineState → Word
opaque setVSpaceRoot_impl : PAddr → Word → MachineRestMonad Unit

def initL2Cache : MachineMonad Unit := machineOpLift initL2Cache_impl
def hwASIDFlush (asid : Word) : MachineMonad Unit := machineOpLift (hwASIDFlush_impl asid)
def sfence : MachineMonad Unit := machineOpLift sfence_impl
def read_stval : MachineMonad Word := NondetM.gets stval_val
def setVSpaceRoot (pt : PAddr) (asid : Word) : MachineMonad Unit := machineOpLift (setVSpaceRoot_impl pt asid)

end Sel4Lean.Spec.MachineOps
