-- SPDX-License-Identifier: GPL-2.0-only (derived from seL4/l4v, https://github.com/seL4/l4v)
import Sel4Lean.Exec.Prelude

/-!
# Stubs: everything the notifications slice uses but does not translate (hand-written)

Each is `opaque`: Lean knows its type and nothing about its behaviour. Proofs about the slice (C4)
take the matching l4v lemmas as hypotheses (e.g. `setThreadState_corres`), the same way
`cancelSignal_corres` in `IpcCancel_R.thy` uses lemmas proved in other files.

Walk replaces these with translations of their own modules.
-/

namespace Sel4Lean.Exec

noncomputable section

/-! ## Opaque types

`opaque X : NonemptyType` gives a type we know nothing about except that it has elements
(the standard Lean pattern). Unknown values are then `Classical.choice`, i.e. unspecified. -/

opaque KernelStateImpl : NonemptyType
/-- l4v `kernel_state` (Haskell `KernelState`): opaque for the slice. -/
def KernelState : Type := KernelStateImpl.type
instance : Nonempty KernelState := KernelStateImpl.property

/-- Haskell `Kernel`, modelled as l4v does: `(kernel_state, 'a) nondet_monad`. -/
abbrev Kernel := NondetM KernelState

opaque TCBImpl : NonemptyType
def TCB : Type := TCBImpl.type
opaque EndpointImpl : NonemptyType
def Endpoint : Type := EndpointImpl.type
opaque CapabilityImpl : NonemptyType
def Capability : Type := CapabilityImpl.type
instance : Nonempty Capability := CapabilityImpl.property
opaque RegisterImpl : NonemptyType
def Register : Type := RegisterImpl.type
instance : Inhabited Register := ⟨Classical.choice RegisterImpl.property⟩
opaque UserContextImpl : NonemptyType
def UserContext : Type := UserContextImpl.type

/-- Haskell `UserMonad` (register-level code run by `asUser`). -/
abbrev UserMonad := NondetM UserContext

/-! ## Functions outside the slice (signatures copied from l4v's Haskell model) -/

-- SEL4.Model.PSpace (typeclass-generic in Haskell; here per use)
opaque getObject {α : Type} : PPtr α → Kernel α
opaque setObject {α : Type} : PPtr α → α → Kernel Unit

-- SEL4.Object.TCB / SEL4.Kernel.Thread
opaque asUser {α : Type} : PPtr TCB → UserMonad α → Kernel α
opaque setRegister : Register → Word → UserMonad Unit
opaque badgeRegister : Register
opaque possibleSwitchTo : PPtr TCB → Kernel Unit
opaque tcbSchedEnqueue : PPtr TCB → Kernel Unit
opaque rescheduleRequired : Kernel Unit

-- SEL4.Object.Endpoint
opaque cancelIPC : PPtr TCB → Kernel Unit

-- SEL4.Model.StateData
opaque ksReadyQueues_asrt : KernelState → Bool

end

end Sel4Lean.Exec
