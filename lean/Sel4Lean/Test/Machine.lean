import Sel4Lean.Spec.MachineOps
import Sel4Lean.Tactic.WP

/-! Tests: the machine state model (W3). Machine operations act on `ksMachineState` through
`doMachineOp`, and their effect is provable with `wp`, as in l4v. -/

namespace Sel4Lean.Test
open Sel4Lean.NondetM
open Sel4Lean.Spec
open Sel4Lean.Spec.MachineOps

/-- `maskInterrupt m irq` sets exactly that mask bit. -/
example (m : Bool) (irq : RISCV64.IRQ) :
    ⟪fun _ => True⟫ (maskInterrupt m irq) ⟪fun _ ms => ms.irq_masks irq = m⟫ := by
  unfold maskInterrupt; wpsimp

/-- Lifted to the kernel: the kernel's machine state records the mask, and nothing else changes. -/
example (m : Bool) (irq : RISCV64.IRQ) (ks₀ : KernelState) :
    ⟪fun ks => ks = ks₀⟫ (doMachineOp (maskInterrupt m irq))
      ⟪fun _ ks => ks.ksMachineState.irq_masks irq = m ∧ ks.ksPSpace = ks₀.ksPSpace⟫ := by
  refine hoare_pre (doMachineOp_wp (P := fun _ => True) (Q := fun _ ms => ms.irq_masks irq = m)
    (by unfold maskInterrupt; wpsimp)
    (fun _ ks => ks.ksMachineState.irq_masks irq = m ∧ ks.ksPSpace = ks₀.ksPSpace)) ?_
  rintro ks rfl; exact ⟨trivial, fun _ _ hq => ⟨hq, rfl⟩⟩

/-- The IRQ oracle's bound is a theorem (l4v: an axiom). -/
example (n : Nat) : irq_oracle n ≤ MachineOps.maxIRQ := irq_oracle_max_irq n

end Sel4Lean.Test
