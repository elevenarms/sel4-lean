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

/-! ## `Ord` -/

/-- Haskell `Ord`: ordered keys with decidable comparisons (used by `Data.Map` operations). -/
class OrdH (k : Type) extends LT k, LE k where
  decLt : DecidableRel (α := k) (· < ·)
  decLe : DecidableRel (α := k) (· ≤ ·)

instance {n : Nat} : OrdH (BitVec n) := ⟨inferInstance, inferInstance⟩
instance : OrdH Nat := ⟨inferInstance, inferInstance⟩
instance {k : Type} [OrdH k] : DecidableRel (α := k) (· < ·) := OrdH.decLt
instance {k : Type} [OrdH k] : DecidableRel (α := k) (· ≤ ·) := OrdH.decLe

/-! ## `MonadFail` (the Haskell spec is polymorphic over failing monads; l4v instantiates them) -/

/-- Haskell `MonadFail`: monads with a failure. -/
class MonadFailH (m : Type → Type) where
  failM {α : Type} : m α

instance {σ : Type} : MonadFailH (NondetM σ) := ⟨NondetM.fail⟩
instance {ε : Type} {m : Type → Type} [Monad m] [MonadFailH m] : MonadFailH (ExceptT ε m) :=
  ⟨ExceptT.lift MonadFailH.failM⟩
instance {σ : Type} {m : Type → Type} [Monad m] [MonadFailH m] : MonadFailH (StateT σ m) :=
  ⟨StateT.lift MonadFailH.failM⟩
instance {ρ : Type} {m : Type → Type} [MonadFailH m] : MonadFailH (ReaderT ρ m) :=
  ⟨fun _ => MonadFailH.failM⟩

/-- Haskell `fail msg` in any failing monad (message dropped, as l4v's `haskell_fail`). -/
abbrev failM {m : Type → Type} {α : Type} [MonadFailH m] (_msg : String) : m α := MonadFailH.failM

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
instance : IntegralH Bool := ⟨fun b => if b then 1 else 0, fun i => i != 0⟩

instance {α : Type} : IntegralH (Sel4Lean.Exec.PPtr α) := ⟨fun p => p.ptr.toNat, fun i => ⟨BitVec.ofInt 64 i⟩⟩

/-- Haskell `fromEnum` / `toEnum` (enumerations are `IntegralH` via their constructor index). -/
abbrev fromEnum {α : Type} [IntegralH α] (x : α) : Nat := (IntegralH.toInt x).toNat
abbrev toEnum {α : Type} [IntegralH α] (i : Nat) : α := IntegralH.ofInt i

/-- Haskell `fromIntegral` (unsigned words convert through their natural-number value, like `ucast`). -/
abbrev fromIntegral {α β : Type} [IntegralH α] [IntegralH β] (x : α) : β :=
  IntegralH.ofInt (IntegralH.toInt x)

/-- Haskell `bit :: Bits a => Int -> a` (used at words and at Int/Nat). -/
abbrev bit {α : Type} [IntegralH α] (i : Nat) : α := IntegralH.ofInt ((2 : Int) ^ i)
abbrev testBit {n : Nat} (x : BitVec n) (i : Nat) : Bool := x.getLsbD i
abbrev complement {n : Nat} (x : BitVec n) : BitVec n := ~~~x
abbrev finiteBitSize {n : Nat} (_ : BitVec n) : Nat := n
abbrev div {α : Type} [Div α] (a b : α) : α := a / b
abbrev «mod» {α : Type} [Mod α] (a b : α) : α := a % b

/-! ## Functions, pairs, Maybe -/

/-- Haskell `show`: only used to build error and debug messages, which the model drops. -/
abbrev «show» {α : Type} (_ : α) : String := ""

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
abbrev filterM {m : Type → Type} [Monad m] {α : Type} (p : α → m Bool) (xs : List α) : m (List α) :=
  xs.filterM p
abbrev foldr {α β : Type} (f : α → β → β) (z : β) (xs : List α) : β := xs.foldr f z
abbrev take {α : Type} (n : Nat) (xs : List α) : List α := xs.take n
abbrev drop {α : Type} (n : Nat) (xs : List α) : List α := xs.drop n
abbrev zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := xs.zip ys
abbrev null {α : Type} (xs : List α) : Bool := xs.isEmpty
abbrev filter {α : Type} (p : α → Bool) (xs : List α) : List α := xs.filter p
abbrev concat {α : Type} (xss : List (List α)) : List α := xss.flatten
abbrev concatMap {α β : Type} (f : α → List β) (xs : List α) : List β := xs.flatMap f
abbrev replicate {α : Type} (n : Nat) (x : α) : List α := List.replicate n x
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

/-! ## `Data.Map` over the function model `k → Option v` (l4v models `psMap` as a function too) -/

namespace Sel4Lean.Spec.MapH
open Classical

variable {k v : Type}

abbrev lookup (key : k) (m : k → Option v) : Option v := m key
abbrev empty : k → Option v := fun _ => none
abbrev insert [DecidableEq k] (key : k) (x : v) (m : k → Option v) : k → Option v :=
  fun y => if y = key then some x else m y
abbrev delete [DecidableEq k] (key : k) (m : k → Option v) : k → Option v :=
  fun y => if y = key then none else m y

/-- `Data.Map.split k m`: the entries strictly below and strictly above `k`. -/
abbrev split [OrdH k] (key : k) (m : k → Option v) :
    (k → Option v) × (k → Option v) :=
  (fun y => if y < key then m y else none, fun y => if key < y then m y else none)

abbrev splitLookup [OrdH k] (key : k) (m : k → Option v) :
    (k → Option v) × Option v × (k → Option v) :=
  ((split key m).1, m key, (split key m).2)

/-- Whole-domain operations are noncomputable over a function model (as Isabelle's `dom`, `Max`). -/
noncomputable def null (m : k → Option v) : Bool := if ∀ y, m y = none then true else false

noncomputable def findMax [OrdH k] [Inhabited k] [Inhabited v] (m : k → Option v) : k × v :=
  Classical.epsilon (fun p : k × v => m p.1 = some p.2 ∧ ∀ y, m y ≠ none → y ≤ p.1)

noncomputable def findMin [OrdH k] [Inhabited k] [Inhabited v] (m : k → Option v) : k × v :=
  Classical.epsilon (fun p : k × v => m p.1 = some p.2 ∧ ∀ y, m y ≠ none → p.1 ≤ y)

/-- `Data.Map.keys`: TODO(W3) needs a finiteness argument to list a function's domain; unspecified for now. -/
opaque keys [Inhabited k] (m : k → Option v) : List k

end Sel4Lean.Spec.MapH
