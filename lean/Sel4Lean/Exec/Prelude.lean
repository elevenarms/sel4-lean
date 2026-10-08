import Sel4Lean.Monad.Nondet

/-!
# Prelude for the translated Haskell kernel model (hand-written)

What l4v's Haskell model gets from GHC's Prelude and `SEL4.Machine` / `SEL4.Model`, restated on top of
`NondetM`. hs2lean's output imports this file and `Stubs.lean`.

The Haskell `Kernel` monad is deterministic. As in l4v's Isabelle translation, the translated model runs
in the **nondeterministic** monad, which is what `corres` is stated over.
-/

namespace Sel4Lean.Exec
open NondetM

instance {σ α : Type} : Inhabited (NondetM σ α) := ⟨NondetM.fail⟩

/-- Haskell `Word` on RISCV64 (l4v `machine_word = 64 word`). -/
abbrev Word := BitVec 64

/-- Haskell `PPtr a`: a kernel pointer tagged with the type of object it points to. -/
structure PPtr (α : Type) where
  ptr : Word
  deriving Inhabited

/-- Equality is on the address. Written by hand: `deriving DecidableEq` would demand `DecidableEq α`
for the phantom tag (`TCB`, `Notification`, …), which is meaningless. -/
instance {α : Type} : DecidableEq (PPtr α) := fun a b =>
  if h : a.ptr = b.ptr then
    isTrue (by cases a; cases b; cases h; rfl)
  else
    isFalse (fun e => h (congrArg PPtr.ptr e))

-- Haskell derives Num, Ord and Bits for `PPtr`: lift them through the address
instance {α : Type} {n : Nat} : OfNat (PPtr α) n := ⟨⟨OfNat.ofNat n⟩⟩
instance {α : Type} : LE (PPtr α) := ⟨fun a b => a.ptr ≤ b.ptr⟩
instance {α : Type} : LT (PPtr α) := ⟨fun a b => a.ptr < b.ptr⟩
instance {α : Type} (a b : PPtr α) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.ptr ≤ b.ptr))
instance {α : Type} (a b : PPtr α) : Decidable (a < b) := inferInstanceAs (Decidable (a.ptr < b.ptr))
instance {α : Type} : Add (PPtr α) := ⟨fun a b => ⟨a.ptr + b.ptr⟩⟩
instance {α : Type} : Sub (PPtr α) := ⟨fun a b => ⟨a.ptr - b.ptr⟩⟩
instance {α : Type} : Mul (PPtr α) := ⟨fun a b => ⟨a.ptr * b.ptr⟩⟩
instance {α : Type} : AndOp (PPtr α) := ⟨fun a b => ⟨a.ptr &&& b.ptr⟩⟩
instance {α : Type} : OrOp (PPtr α) := ⟨fun a b => ⟨a.ptr ||| b.ptr⟩⟩
instance {α : Type} : HShiftLeft (PPtr α) Nat (PPtr α) := ⟨fun a k => ⟨a.ptr <<< k⟩⟩
instance {α : Type} : HShiftRight (PPtr α) Nat (PPtr α) := ⟨fun a k => ⟨a.ptr >>> k⟩⟩

/-- Haskell `Foreign.Ptr a`: a raw machine address (used only by machine-interface code). -/
abbrev PtrH (_ : Type) := Word

/-- Haskell `fail msg` in the kernel monad: l4v translates it to failure, dropping the message. -/
abbrev failH {σ α : Type} (_msg : String) : NondetM σ α := NondetM.fail

/-- Haskell `assert c msg` (l4v `haskell_assert`): fail unless `c`. -/
abbrev assertH {σ : Type} (c : Bool) (_msg : String) : NondetM σ Unit := NondetM.assertM (c = true)

/-- Haskell `stateAssert P msg` (l4v `stateAssert`). -/
abbrev stateAssertH {σ : Type} (P : σ → Bool) (_msg : String) : NondetM σ Unit :=
  NondetM.stateAssert (fun s => P s = true)

/-- Haskell `forM_ xs f`. -/
abbrev forM_H {σ α β : Type} (xs : List α) (f : α → NondetM σ β) : NondetM σ Unit := NondetM.mapM_x f xs

/-- Haskell `Data.List.delete x xs`: remove the first occurrence (l4v: `remove1`). -/
abbrev deleteH {α : Type} [BEq α] (x : α) (xs : List α) : List α := xs.erase x

end Sel4Lean.Exec
