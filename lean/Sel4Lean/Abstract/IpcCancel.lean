-- SPDX-License-Identifier: GPL-2.0-only (derived from seL4/l4v, https://github.com/seL4/l4v)
import Sel4Lean.Monad.Nondet

/-!
# Abstract spec slice: notifications (hand-translated from Isabelle)

From l4v `spec/abstract/Structures_A.thy`, `KHeap_A.thy`, `IpcCancel_A.thy` (l4v ac4a36d).
Translated by hand for crawl (roadmap C3); names keep l4v's spelling so the two can be compared line by line.

Like `Exec/Stubs.lean`, everything outside the slice is opaque: the abstract state, the object heap accessors
and `set_thread_state`. C4 assumes their l4v lemmas as hypotheses.
-/

namespace Sel4Lean.Abstract
open NondetM

noncomputable section

/-- l4v `obj_ref` (= `machine_word`, 64-bit on RISCV64). -/
abbrev ObjRef := BitVec 64
/-- l4v `badge` (= `data` = `machine_word`). -/
abbrev Badge := BitVec 64

opaque StateImpl : NonemptyType
/-- l4v `'z state` (abstract kernel state): opaque for the slice. -/
def State : Type := StateImpl.type
/-- l4v `('a,'z) s_monad = ('z state, 'a) nondet_monad`. -/
abbrev SMonad := NondetM State

/-- l4v `datatype ntfn` (Structures_A.thy:303). -/
inductive Ntfn where
  | IdleNtfn
  | WaitingNtfn (queue : List ObjRef)
  | ActiveNtfn (badge : Badge)
  deriving Inhabited, DecidableEq

/-- l4v `record notification` (Structures_A.thy:308). -/
structure Notification where
  ntfn_obj : Ntfn
  ntfn_bound_tcb : Option ObjRef
  deriving Inhabited

/-- l4v `ntfn_set_obj` (record update abbreviation). -/
def ntfn_set_obj (n : Notification) (o : Ntfn) : Notification := { n with ntfn_obj := o }

opaque ReceiverPayloadImpl : NonemptyType
def ReceiverPayload : Type := ReceiverPayloadImpl.type
opaque SenderPayloadImpl : NonemptyType
def SenderPayload : Type := SenderPayloadImpl.type

/-- l4v `datatype thread_state` (Structures_A.thy:362). -/
inductive ThreadState where
  | Running
  | Inactive
  | Restart
  | BlockedOnReceive (ep : ObjRef) (payload : ReceiverPayload)
  | BlockedOnSend (ep : ObjRef) (payload : SenderPayload)
  | BlockedOnReply
  | BlockedOnNotification (ntfn : ObjRef)
  | IdleThreadState

instance : Inhabited ThreadState := ⟨.Running⟩

/-- l4v `get_notification ≡ get_simple_ko Notification` (KHeap_A.thy:166). -/
opaque get_notification : ObjRef → SMonad Notification
/-- l4v `set_notification ≡ set_simple_ko Notification` (KHeap_A.thy:170). -/
opaque set_notification : ObjRef → Notification → SMonad Unit
/-- l4v `set_thread_state` (TcbAcc_A.thy). -/
opaque set_thread_state : ObjRef → ThreadState → SMonad Unit

/-- l4v `cancel_signal` (IpcCancel_A.thy:328):
```
cancel_signal threadptr ntfnptr ≡ do
  ntfn ← get_notification ntfnptr;
  queue ← (case ntfn_obj ntfn of WaitingNtfn queue ⇒ return queue | _ ⇒ fail);
  queue' ← return $ remove1 threadptr queue;
  newNTFN ← return $ ntfn_set_obj ntfn (case queue' of [] ⇒ IdleNtfn | _ ⇒ WaitingNtfn queue');
  set_notification ntfnptr newNTFN;
  set_thread_state threadptr Inactive
od
``` -/
def cancel_signal (threadptr ntfnptr : ObjRef) : SMonad Unit := do
  let ntfn ← get_notification ntfnptr
  let queue ← (match ntfn.ntfn_obj with
    | .WaitingNtfn queue => pure queue
    | _ => NondetM.fail)
  let queue' ← pure (queue.erase threadptr)
  let newNTFN ← pure (ntfn_set_obj ntfn (match queue' with
    | [] => .IdleNtfn
    | _ => .WaitingNtfn queue'))
  set_notification ntfnptr newNTFN
  set_thread_state threadptr .Inactive

/-- `remove1` (Isabelle) and `List.erase` (Lean) agree: both drop the first occurrence. -/
example : ([1, 2, 1, 3] : List Nat).erase 1 = [2, 1, 3] := rfl

end
end Sel4Lean.Abstract
