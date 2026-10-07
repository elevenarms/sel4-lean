/-!
# Nondeterministic state monad with failure

Port of l4v `lib/Monads/nondet/Nondet_Monad.thy`:

```
type_synonym ('s, 'a) nondet_monad = "'s ⇒ ('a × 's) set × bool"
```

A computation maps a state to the **set** of possible `(result, state)` pairs and a **failure flag**.
Sets are predicates (no Mathlib), and the failure flag is a `Prop`.

Definitions follow l4v one to one. The `Monad` instance means Lean `do`-notation means l4v's `do … od`.
-/

namespace Sel4Lean

/-- l4v `('s, 'a) nondet_monad`. `(m s).1` is the result set, `(m s).2` the failure flag. -/
def NondetM (σ α : Type) : Type := σ → ((α × σ) → Prop) × Prop

namespace NondetM

variable {σ α β γ : Type}

/-- Result set of `m` in state `s`. -/
abbrev results (m : NondetM σ α) (s : σ) : (α × σ) → Prop := (m s).1

/-- Failure flag of `m` in state `s`. -/
abbrev failed (m : NondetM σ α) (s : σ) : Prop := (m s).2

/-- l4v `return a ≡ λs. ({(a,s)}, False)` -/
def ret (a : α) : NondetM σ α := fun s => (fun p => p = (a, s), False)

/-- l4v `bind f g ≡ λs. (⋃(fst ` case_prod g ` fst (f s)), True ∈ snd ` case_prod g ` fst (f s) ∨ snd (f s))` -/
def bind (f : NondetM σ α) (g : α → NondetM σ β) : NondetM σ β := fun s =>
  ( fun p => ∃ r t, (f s).1 (r, t) ∧ (g r t).1 p,
    (∃ r t, (f s).1 (r, t) ∧ (g r t).2) ∨ (f s).2 )

instance : Monad (NondetM σ) where
  pure := ret
  bind := bind

/-- l4v `get ≡ λs. ({(s,s)}, False)` -/
def get : NondetM σ σ := fun s => (fun p => p = (s, s), False)

/-- l4v `put s ≡ λ_. ({((),s)}, False)` -/
def put (s : σ) : NondetM σ Unit := fun _ => (fun p => p = ((), s), False)

/-- l4v `fail ≡ λs. ({}, True)` -/
def fail : NondetM σ α := fun _ => (fun _ => False, True)

/-- l4v `select A ≡ λs. (A × {s}, False)` -/
def select (A : α → Prop) : NondetM σ α := fun s => (fun p => A p.1 ∧ p.2 = s, False)

/-- l4v `f ⊓ g`: either computation may run. -/
def alternative (f g : NondetM σ α) : NondetM σ α := fun s =>
  (fun p => (f s).1 p ∨ (g s).1 p, (f s).2 ∨ (g s).2)

/-- l4v `assert P ≡ if P then return () else fail` (renamed: `assert` is a Lean `do` element). -/
def assertM (P : Prop) [Decidable P] : NondetM σ Unit := if P then ret () else fail

/-- l4v `assert_opt` -/
def assertOpt : Option α → NondetM σ α
  | none => fail
  | some v => ret v

/-- l4v `gets f ≡ get >>= (λs. return (f s))` -/
def gets (f : σ → α) : NondetM σ α := bind get (fun s => ret (f s))

/-- l4v `modify f ≡ get >>= (λs. put (f s))` -/
def modify (f : σ → σ) : NondetM σ Unit := bind get (fun s => put (f s))

/-- l4v `state_assert P ≡ get >>= (λs. assert (P s))` -/
def stateAssert (P : σ → Prop) [DecidablePred P] : NondetM σ Unit := bind get (fun s => assertM (P s))

/-- l4v `when P m` (renamed: `when`/`unless` are Lean keywords). `when P m ≡ if P then m else return ()` -/
def whenM (P : Prop) [Decidable P] (m : NondetM σ Unit) : NondetM σ Unit := if P then m else ret ()

/-- l4v `unless P m ≡ when (¬P) m` -/
def unlessM (P : Prop) [Decidable P] (m : NondetM σ Unit) : NondetM σ Unit := whenM (¬P) m

/-- l4v `condition P L R ≡ λs. if P s then L s else R s` -/
def condition (P : σ → Prop) [DecidablePred P] (L R : NondetM σ α) : NondetM σ α :=
  fun s => if P s then L s else R s

/-- l4v `mapM_x f xs`: run `f` on each element left to right, discarding results. -/
def mapM_x (f : α → NondetM σ β) : List α → NondetM σ Unit
  | [] => ret ()
  | x :: xs => bind (f x) (fun _ => mapM_x f xs)

/-! ## Unfolding lemmas -/

@[simp] theorem pure_eq (a : α) : (pure a : NondetM σ α) = ret a := rfl
@[simp] theorem bind_eq (f : NondetM σ α) (g : α → NondetM σ β) : (f >>= g) = bind f g := rfl

@[simp] theorem ret_results (a : α) (s : σ) (p : α × σ) : (ret a s).1 p ↔ p = (a, s) := Iff.rfl
@[simp] theorem ret_failed (a : α) (s : σ) : (ret a s).2 ↔ False := Iff.rfl
@[simp] theorem get_results (s : σ) (p : σ × σ) : (get s).1 p ↔ p = (s, s) := Iff.rfl
@[simp] theorem get_failed (s : σ) : (get s).2 ↔ False := Iff.rfl
@[simp] theorem put_results (s' s : σ) (p : Unit × σ) : (put s' s).1 p ↔ p = ((), s') := Iff.rfl
@[simp] theorem put_failed (s' s : σ) : (put s' s).2 ↔ False := Iff.rfl
@[simp] theorem fail_results (s : σ) (p : α × σ) : ((fail : NondetM σ α) s).1 p ↔ False := Iff.rfl
@[simp] theorem fail_failed (s : σ) : ((fail : NondetM σ α) s).2 ↔ True := Iff.rfl

@[simp] theorem bind_results (f : NondetM σ α) (g : α → NondetM σ β) (s : σ) (p : β × σ) :
    (bind f g s).1 p ↔ ∃ r t, (f s).1 (r, t) ∧ (g r t).1 p := Iff.rfl
@[simp] theorem bind_failed (f : NondetM σ α) (g : α → NondetM σ β) (s : σ) :
    (bind f g s).2 ↔ (∃ r t, (f s).1 (r, t) ∧ (g r t).2) ∨ (f s).2 := Iff.rfl

/-- l4v `simpler_gets_def` -/
theorem gets_eq (f : σ → α) : gets f = fun s => (fun p => p = (f s, s), False) := by
  funext s
  simp only [gets, bind, get, ret]
  congr 1
  · funext p; apply propext; constructor
    · rintro ⟨r, t, h1, h2⟩; cases h1; exact h2
    · intro h; exact ⟨s, s, rfl, h⟩
  · apply propext; constructor
    · rintro (⟨r, t, _, h⟩ | h) <;> exact h
    · intro h; exact h.elim

/-- l4v `simpler_modify_def` -/
theorem modify_eq (f : σ → σ) : modify f = fun s => (fun p => p = ((), f s), False) := by
  funext s
  simp only [modify, bind, get, put]
  congr 1
  · funext p; apply propext; constructor
    · rintro ⟨r, t, h1, h2⟩; cases h1; exact h2
    · intro h; exact ⟨s, s, rfl, h⟩
  · apply propext; constructor
    · rintro (⟨r, t, _, h⟩ | h) <;> exact h
    · intro h; exact h.elim

/-! ## Monad laws (l4v `return_bind`, `bind_return`, `bind_assoc`) -/

theorem ret_bind (a : α) (g : α → NondetM σ β) : bind (ret a) g = g a := by
  funext s
  show (_, _) = g a s
  apply Prod.ext
  · funext p; apply propext; simp only [ret]; constructor
    · rintro ⟨r, t, h1, h2⟩; cases h1; exact h2
    · intro h; exact ⟨a, s, rfl, h⟩
  · apply propext; simp only [ret]; constructor
    · rintro (⟨r, t, h1, h2⟩ | h)
      · cases h1; exact h2
      · exact h.elim
    · intro h; exact Or.inl ⟨a, s, rfl, h⟩

theorem bind_ret (f : NondetM σ α) : bind f ret = f := by
  funext s
  show (_, _) = f s
  apply Prod.ext
  · funext p; apply propext; simp only [ret]; constructor
    · rintro ⟨r, t, h1, h2⟩; cases h2; exact h1
    · intro h; exact ⟨p.1, p.2, h, rfl⟩
  · apply propext; simp only [ret]; constructor
    · rintro (⟨r, t, _, h⟩ | h)
      · exact h.elim
      · exact h
    · intro h; exact Or.inr h

theorem bind_assoc (f : NondetM σ α) (g : α → NondetM σ β) (h : β → NondetM σ γ) :
    bind (bind f g) h = bind f (fun x => bind (g x) h) := by
  funext s
  apply Prod.ext
  · funext p; apply propext; simp only [bind]; constructor
    · rintro ⟨r, t, ⟨r', t', h1, h2⟩, h3⟩; exact ⟨r', t', h1, r, t, h2, h3⟩
    · rintro ⟨r', t', h1, r, t, h2, h3⟩; exact ⟨r, t, ⟨r', t', h1, h2⟩, h3⟩
  · apply propext; simp only [bind]; constructor
    · rintro (⟨r, t, ⟨r', t', h1, h2⟩, h3⟩ | (⟨r', t', h1, h2⟩ | h1))
      · exact Or.inl ⟨r', t', h1, Or.inl ⟨r, t, h2, h3⟩⟩
      · exact Or.inl ⟨r', t', h1, Or.inr h2⟩
      · exact Or.inr h1
    · rintro (⟨r', t', h1, (⟨r, t, h2, h3⟩ | h2)⟩ | h1)
      · exact Or.inl ⟨r, t, ⟨r', t', h1, h2⟩, h3⟩
      · exact Or.inr (Or.inl ⟨r', t', h1, h2⟩)
      · exact Or.inr (Or.inr h1)

end NondetM
end Sel4Lean
