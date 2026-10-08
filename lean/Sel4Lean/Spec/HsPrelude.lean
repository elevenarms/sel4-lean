import Sel4Lean.Monad.Nondet
import Sel4Lean.Exec.Prelude

/-!
# Haskell Prelude / base library for translated modules (hand-written, W2)

What the translated kernel model uses from GHC's `Prelude`, `Data.Bits`, `Data.List`, `Data.Maybe` and
`Control.Monad`, restated over `NondetM`, following how l4v's Isabelle library models them
(`haskell_fail`, `undefined`, `ucast`, …). Partial Haskell functions (`head`, `fromJust`, `error`) return
`default`; inside the kernel monad `default` is `fail`, matching l4v's treatment.
-/

namespace Sel4Lean.Spec
open Sel4Lean (NondetM)

/-! ## Errors -/

/-- Haskell `error msg`: bottom. As a kernel computation this is `fail` (`default` of `NondetM`). -/
abbrev error {α : Type} [Inhabited α] (_msg : String) : α := default
/-- Haskell `undefined` (l4v: `undefined`). -/
abbrev undefined {α : Type} [Inhabited α] : α := default

/-! ## Numbers and bits -/

/-- Integral types, for `fromIntegral` (l4v: `ucast` / `of_nat` / `unat`). -/
class IntegralH (α : Type) where
  toInt : α → Int
  ofInt : Int → α

instance {n : Nat} : IntegralH (BitVec n) := ⟨fun x => x.toNat, fun i => BitVec.ofInt n i⟩
instance : IntegralH Int := ⟨id, id⟩
instance : IntegralH Nat := ⟨Int.ofNat, Int.toNat⟩

/-- Haskell `fromIntegral` (unsigned words convert through their natural-number value, like `ucast`). -/
abbrev fromIntegral {α β : Type} [IntegralH α] [IntegralH β] (x : α) : β :=
  IntegralH.ofInt (IntegralH.toInt x)

abbrev bit {n : Nat} (i : Nat) : BitVec n := 1#n <<< i
abbrev testBit {n : Nat} (x : BitVec n) (i : Nat) : Bool := x.getLsbD i
abbrev complement {n : Nat} (x : BitVec n) : BitVec n := ~~~x
abbrev finiteBitSize {n : Nat} (_ : BitVec n) : Nat := n
abbrev div {α : Type} [Div α] (a b : α) : α := a / b
abbrev «mod» {α : Type} [Mod α] (a b : α) : α := a % b

/-! ## Functions, pairs, Maybe -/

abbrev const {α β : Type} (a : α) (_ : β) : α := a
abbrev fst {α β : Type} (p : α × β) : α := p.1
abbrev snd {α β : Type} (p : α × β) : β := p.2
abbrev maybe {α β : Type} (d : β) (f : α → β) : Option α → β
  | none => d
  | some a => f a
abbrev fromJust {α : Type} [Inhabited α] : Option α → α
  | some a => a
  | none => default
abbrev isJust {α : Type} (o : Option α) : Bool := o.isSome
abbrev isNothing {α : Type} (o : Option α) : Bool := o.isNone

/-! ## Lists -/

abbrev map {α β : Type} (f : α → β) (xs : List α) : List β := xs.map f
abbrev length {α : Type} (xs : List α) : Int := xs.length
abbrev head {α : Type} [Inhabited α] (xs : List α) : α := xs.headD default
abbrev tail {α : Type} (xs : List α) : List α := xs.tail
abbrev reverse {α : Type} (xs : List α) : List α := xs.reverse
abbrev takeWhile {α : Type} (p : α → Bool) (xs : List α) : List α := xs.takeWhile p
abbrev elem {α : Type} [BEq α] (x : α) (xs : List α) : Bool := xs.contains x
abbrev notElem {α : Type} [BEq α] (x : α) (xs : List α) : Bool := !xs.contains x
abbrev foldl' {α β : Type} (f : β → α → β) (z : β) (xs : List α) : β := xs.foldl f z
abbrev listIndexH {α : Type} [Inhabited α] (xs : List α) (i : Int) : α := xs.getD i.toNat default
abbrev enumFromToH {α : Type} [IntegralH α] (a b : α) : List α :=
  (List.range ((IntegralH.toInt b - IntegralH.toInt a + 1).toNat)).map
    (fun (k : Nat) => IntegralH.ofInt (IntegralH.toInt a + Int.ofNat k))

/-- Haskell `arr // [(i, v), …]` on arrays, which l4v (and this translation) model as functions. -/
abbrev arrayUpdH {ι ε : Type} [BEq ι] (arr : ι → ε) (upds : List (ι × ε)) : ι → ε :=
  fun i => match upds.reverse.find? (fun p => p.1 == i) with
    | some p => p.2
    | none => arr i

/-! ## Monads -/

abbrev gets {σ α : Type} (f : σ → α) : NondetM σ α := NondetM.gets f
abbrev modify {σ : Type} (f : σ → σ) : NondetM σ Unit := NondetM.modify f
abbrev whenH {m : Type → Type} [Monad m] (c : Bool) (x : m Unit) : m Unit := if c then x else pure ()
abbrev unlessH {m : Type → Type} [Monad m] (c : Bool) (x : m Unit) : m Unit := if c then pure () else x
abbrev liftM {m : Type → Type} [Monad m] {α β : Type} (f : α → β) (x : m α) : m β := f <$> x
abbrev mapM {m : Type → Type} [Monad m] {α β : Type} (f : α → m β) (xs : List α) : m (List β) := xs.mapM f
abbrev mapM_ {m : Type → Type} [Monad m] {α β : Type} (f : α → m β) (xs : List α) : m Unit :=
  xs.forM (fun x => do let _ ← f x; pure ())
abbrev zipWithM_ {m : Type → Type} [Monad m] {α β γ : Type} (f : α → β → m γ) (xs : List α) (ys : List β) :
    m Unit := mapM_ (fun p => f p.1 p.2) (xs.zip ys)
abbrev zipWithM {m : Type → Type} [Monad m] {α β γ : Type} (f : α → β → m γ) (xs : List α) (ys : List β) :
    m (List γ) := mapM (fun p => f p.1 p.2) (xs.zip ys)
abbrev foldM {m : Type → Type} [Monad m] {α β : Type} (f : β → α → m β) (z : β) (xs : List α) : m β :=
  xs.foldlM f z
abbrev lift {m n : Type → Type} [MonadLift m n] {α : Type} (x : m α) : n α := MonadLift.monadLift x
abbrev seqH {m : Type → Type} [Monad m] {α β : Type} (f : m (α → β)) (x : m α) : m β := f <*> x

end Sel4Lean.Spec
