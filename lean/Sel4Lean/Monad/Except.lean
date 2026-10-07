import Sel4Lean.Monad.VCG

/-!
# Exception monad on top of `NondetM`

Port of l4v's exception layer in `Nondet_Monad.thy` / `Nondet_VCG.thy`:

```
returnOk ≡ return o Inr        throwError ≡ return o Inl
liftE f  ≡ f >>= (λr. return (Inr r))
f >>=E g ≡ f >>= lift g
validE P f Q E ≡ valid P f (λv s. case v of Inr r ⇒ Q r s | Inl e ⇒ E e s)
```

l4v's `'e + 'a` (`Inl` = error) becomes Lean's `Except ε α` (`.error` / `.ok`).
-/

namespace Sel4Lean
namespace NondetM

variable {σ ε α β : Type}

/-- l4v `returnOk` -/
def returnOk (a : α) : NondetM σ (Except ε α) := ret (.ok a)

/-- l4v `throwError` -/
def throwError (e : ε) : NondetM σ (Except ε α) := ret (.error e)

/-- l4v `liftE`: run a computation that cannot throw. -/
def liftE (f : NondetM σ α) : NondetM σ (Except ε α) := bind f (fun r => ret (.ok r))

/-- l4v `lift`: continue on success, pass errors through. -/
def liftK (g : α → NondetM σ (Except ε β)) : Except ε α → NondetM σ (Except ε β)
  | .error e => throwError e
  | .ok a => g a

/-- l4v `f >>=E g` -/
def bindE (f : NondetM σ (Except ε α)) (g : α → NondetM σ (Except ε β)) : NondetM σ (Except ε β) :=
  bind f (liftK g)

/-- l4v `f <catch> handler` -/
def catchE (f : NondetM σ (Except ε α)) (handler : ε → NondetM σ α) : NondetM σ α :=
  bind f fun
    | .ok b => ret b
    | .error e => handler e

/-- Postcondition for an exception computation: `Q` on success, `E` on error. -/
def postE (Q : α → σ → Prop) (E : ε → σ → Prop) : Except ε α → σ → Prop
  | .ok r, s => Q r s
  | .error e, s => E e s

@[simp] theorem postE_ok (Q : α → σ → Prop) (E : ε → σ → Prop) (r : α) (s : σ) :
    postE Q E (.ok r) s ↔ Q r s := Iff.rfl
@[simp] theorem postE_error (Q : α → σ → Prop) (E : ε → σ → Prop) (e : ε) (s : σ) :
    postE Q E (.error e) s ↔ E e s := Iff.rfl

/-- l4v `⦃P⦄ f ⦃Q⦄,⦃E⦄` -/
def validE (P : σ → Prop) (f : NondetM σ (Except ε α)) (Q : α → σ → Prop) (E : ε → σ → Prop) : Prop :=
  valid P f (postE Q E)

theorem returnOk_wp (a : α) (Q : α → σ → Prop) (E : ε → σ → Prop) :
    validE (Q a) (returnOk a) Q E := by
  intro s hs r s' hr; cases hr; exact hs

theorem throwError_wp (e : ε) (Q : α → σ → Prop) (E : ε → σ → Prop) :
    validE (E e) (throwError e) Q E := by
  intro s hs r s' hr; cases hr; exact hs

theorem liftE_wp {P : σ → Prop} {f : NondetM σ α} {Q : α → σ → Prop} (E : ε → σ → Prop)
    (h : valid P f Q) : validE P (liftE f) Q E := by
  intro s hs r s' ⟨x, t, hfx, hr⟩
  obtain ⟨hr1, hr2⟩ := Prod.mk.inj hr
  rw [hr1, hr2]
  exact h s hs x t hfx

/-- l4v `bindE_wp` / `hoare_vcg_seqE` -/
theorem bindE_wp {A : σ → Prop} {B : α → σ → Prop} {C : β → σ → Prop} {E : ε → σ → Prop}
    {f : NondetM σ (Except ε α)} {g : α → NondetM σ (Except ε β)}
    (hg : ∀ x, validE (B x) (g x) C E) (hf : validE A f B E) : validE A (bindE f g) C E := by
  intro s hs r s' ⟨x, t, hfx, hl⟩
  have hpost := hf s hs x t hfx
  cases x with
  | ok a => exact hg a t hpost r s' hl
  | error e =>
    cases hl
    exact hpost

theorem catchE_wp {P : σ → Prop} {f : NondetM σ (Except ε α)} {Q : α → σ → Prop}
    {E : ε → σ → Prop} {handler : ε → NondetM σ α}
    (hh : ∀ e, valid (E e) (handler e) Q) (hf : validE P f Q E) : valid P (catchE f handler) Q := by
  intro s hs r s' ⟨x, t, hfx, hl⟩
  have hpost := hf s hs x t hfx
  cases x with
  | ok b => cases hl; exact hpost
  | error e => exact hh e t hpost r s' hl

end NondetM
end Sel4Lean
