import Sel4Lean.Exec.Gen.Structures

/-!
# Stubs that mention the translated types (hand-written)

Same idea as `Stubs.lean`, but these signatures need `ThreadState` / `Notification`, so they come after
the generated `Gen/Structures.lean`. Signatures copied from l4v's Haskell model.
-/

namespace Sel4Lean.Exec
noncomputable section

-- SEL4.Object.TCB / SEL4.Kernel.Thread
opaque getThreadState : PPtr TCB → Kernel ThreadState
opaque setThreadState : ThreadState → PPtr TCB → Kernel Unit
opaque getBoundNotification : PPtr TCB → Kernel (Option (PPtr Notification))
opaque setBoundNotification : Option (PPtr Notification) → PPtr TCB → Kernel Unit

-- SEL4.Object.Structures (field of the `Capability` type, which the slice does not translate)
opaque capNtfnPtr : Capability → PPtr Notification

end
end Sel4Lean.Exec
