-- SPDX-License-Identifier: GPL-2.0-only (derived from seL4/l4v, https://github.com/seL4/l4v)
import Sel4Lean.Tactic.Crunch
import Sel4Lean.Exec.Gen.Notification

/-!
# W1 test: `crunch` over the whole generated notifications module

If the leaf operations (object access, thread state, `asUser`, scheduling) preserve a property `P` of
the kernel state, then every function of the translated `Notification.lhs` preserves `P`.
l4v uses exactly this pattern (`crunch … for typ_at'[wp]`, `ko_wp_at'`, …).
-/

namespace Sel4Lean.Refine.Crunch
open NondetM Sel4Lean.Exec

/-- Leaf operations preserve `P` (the facts l4v's crunch would find as existing `[wp]` rules). -/
structure LeafPreserve (P : KernelState → Prop) : Prop where
  getObject : ∀ {α : Type} (p : PPtr α), ⟪P⟫ (getObject p) ⟪fun _ => P⟫
  setObject : ∀ {α : Type} (p : PPtr α) (v : α), ⟪P⟫ (setObject p v) ⟪fun _ => P⟫
  getThreadState : ∀ t, ⟪P⟫ (getThreadState t) ⟪fun _ => P⟫
  setThreadState : ∀ st t, ⟪P⟫ (setThreadState st t) ⟪fun _ => P⟫
  asUser : ∀ {α : Type} t (m : UserMonad α), ⟪P⟫ (asUser t m) ⟪fun _ => P⟫
  cancelIPC : ∀ t, ⟪P⟫ (cancelIPC t) ⟪fun _ => P⟫
  possibleSwitchTo : ∀ t, ⟪P⟫ (possibleSwitchTo t) ⟪fun _ => P⟫
  tcbSchedEnqueue : ∀ t, ⟪P⟫ (tcbSchedEnqueue t) ⟪fun _ => P⟫
  rescheduleRequired : ⟪P⟫ rescheduleRequired ⟪fun _ => P⟫
  getBoundNotification : ∀ t, ⟪P⟫ (getBoundNotification t) ⟪fun _ => P⟫
  setBoundNotification : ∀ n t, ⟪P⟫ (setBoundNotification n t) ⟪fun _ => P⟫

crunch (P : KernelState → Prop) (H : LeafPreserve P)
  getNotification setNotification doNBRecvFailedTransfer doUnbindNotification
  sendSignal receiveSignal cancelAllSignals cancelSignal completeSignal
  bindNotification unbindNotification unbindMaybeNotification
  for inv : P with [H.getObject, H.setObject, H.getThreadState, H.setThreadState, H.asUser,
    H.cancelIPC, H.possibleSwitchTo, H.tcbSchedEnqueue, H.rescheduleRequired,
    H.getBoundNotification, H.setBoundNotification]

-- the generated lemmas
#check @cancelSignal_inv
#check @sendSignal_inv

end Sel4Lean.Refine.Crunch
