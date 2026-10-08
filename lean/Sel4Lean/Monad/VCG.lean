import Sel4Lean.Monad.Nondet

/-!
# Hoare logic and weakest preconditions for `NondetM`

Port of l4v `Nondet_VCG.thy` / `Nondet_No_Fail.thy` (core only):

```
valid P f Q   ≡ ∀s. P s ⟶ (∀(r,s') ∈ fst (f s). Q r s')     -- partial correctness
no_fail P m   ≡ ∀s. P s ⟶ ¬snd (m s)
```

Plus the basic `wp` rules and a first `wp` / `wpsimp` tactic. As in l4v, `wp` works backwards from the
postcondition: every rule's precondition is left open, so `apply` computes it by unification.
-/

namespace Sel4Lean
namespace NondetM

variable {σ α β : Type}

/-- l4v `⦃P⦄ f ⦃Q⦄` (partial correctness: says nothing about failure). -/
def valid (P : σ → Prop) (f : NondetM σ α) (Q : α → σ → Prop) : Prop :=
  ∀ s, P s → ∀ r s', (f s).1 (r, s') → Q r s'

/-- l4v `no_fail P m`: from a state satisfying `P`, `m` does not fail. -/
def noFail (P : σ → Prop) (m : NondetM σ α) : Prop :=
  ∀ s, P s → ¬ (m s).2

-- `⦃ ⦄` are binder brackets in Lean, so triples use `⟪ ⟫`. The program is parsed at max precedence:
-- write `⟪P⟫ (bind f g) ⟪Q⟫`, with parentheses around anything that is not atomic.
scoped notation:max "⟪" P "⟫ " f:max " ⟪" Q "⟫" => valid P f Q

/-! ## Structural rules -/

/-- l4v `hoare_weaken_pre` (named `hoare_pre` when used as a wp setup step). -/
theorem hoare_pre {P P' : σ → Prop} {f : NondetM σ α} {Q : α → σ → Prop}
    (h : ⟪P'⟫ f ⟪Q⟫) (hP : ∀ s, P s → P' s) : ⟪P⟫ f ⟪Q⟫ :=
  fun s hs => h s (hP s hs)

/-- l4v `hoare_strengthen_post` -/
theorem hoare_strengthen_post {P : σ → Prop} {f : NondetM σ α} {Q Q' : α → σ → Prop}
    (h : ⟪P⟫ f ⟪Q⟫) (hQ : ∀ r s, Q r s → Q' r s) : ⟪P⟫ f ⟪Q'⟫ :=
  fun s hs r s' hr => hQ r s' (h s hs r s' hr)

/-- l4v `hoare_conj` -/
theorem hoare_conj {P P' : σ → Prop} {f : NondetM σ α} {Q Q' : α → σ → Prop}
    (h : ⟪P⟫ f ⟪Q⟫) (h' : ⟪P'⟫ f ⟪Q'⟫) : ⟪fun s => P s ∧ P' s⟫ f ⟪fun r s => Q r s ∧ Q' r s⟫ :=
  fun s hs r s' hr => ⟨h s hs.1 r s' hr, h' s hs.2 r s' hr⟩

/-- A fact that does not mention the state survives any program. -/
theorem valid_const {R : Prop} {f : NondetM σ α} : ⟪fun _ => R⟫ f ⟪fun _ _ => R⟫ :=
  fun _ hR _ _ _ => hR

/-! ## wp rules: each states the weakest precondition of one primitive -/

theorem ret_wp (a : α) (Q : α → σ → Prop) : ⟪Q a⟫ (ret a) ⟪Q⟫ := by
  intro s hs r s' hr; cases hr; exact hs

theorem pure_wp (a : α) (Q : α → σ → Prop) : ⟪Q a⟫ (pure a) ⟪Q⟫ := ret_wp a Q

/-- l4v `bind_wp` / `hoare_seq_ext`. The continuation goal comes first so `wp` solves it first,
which fixes the intermediate assertion `B` before `f` is processed. -/
theorem bind_wp {A : σ → Prop} {B : α → σ → Prop} {C : β → σ → Prop}
    {f : NondetM σ α} {g : α → NondetM σ β}
    (hg : ∀ x, ⟪B x⟫ (g x) ⟪C⟫) (hf : ⟪A⟫ f ⟪B⟫) : ⟪A⟫ (bind f g) ⟪C⟫ := by
  intro s hs r s' ⟨x, t, hx, hr⟩
  exact hg x t (hf s hs x t hx) r s' hr

theorem bind_wp' {A : σ → Prop} {B : α → σ → Prop} {C : β → σ → Prop}
    {f : NondetM σ α} {g : α → NondetM σ β}
    (hg : ∀ x, ⟪B x⟫ (g x) ⟪C⟫) (hf : ⟪A⟫ f ⟪B⟫) : ⟪A⟫ (f >>= g) ⟪C⟫ := bind_wp hg hf

theorem get_wp (Q : σ → σ → Prop) : ⟪fun s => Q s s⟫ get ⟪Q⟫ := by
  intro s hs r s' hr; cases hr; exact hs

theorem put_wp (s₀ : σ) (Q : Unit → σ → Prop) : ⟪fun _ => Q () s₀⟫ (put s₀) ⟪Q⟫ := by
  intro s hs r s' hr; cases hr; exact hs

theorem gets_wp (f : σ → α) (Q : α → σ → Prop) : ⟪fun s => Q (f s) s⟫ (gets f) ⟪Q⟫ := by
  intro s hs r s' hr; rw [gets_eq] at hr; cases hr; exact hs

theorem modify_wp (f : σ → σ) (Q : Unit → σ → Prop) : ⟪fun s => Q () (f s)⟫ (modify f) ⟪Q⟫ := by
  intro s hs r s' hr; rw [modify_eq] at hr; cases hr; exact hs

theorem fail_wp (Q : α → σ → Prop) : ⟪fun _ => True⟫ (fail : NondetM σ α) ⟪Q⟫ := by
  intro s _ r s' hr; exact hr.elim

theorem assertM_wp (P : Prop) [Decidable P] (Q : Unit → σ → Prop) :
    ⟪fun s => P → Q () s⟫ (assertM P) ⟪Q⟫ := by
  intro s hs r s' hr
  unfold assertM at hr
  split at hr
  · rename_i hP; cases hr; exact hs hP
  · exact hr.elim

theorem assertOpt_wp (v : Option α) (Q : α → σ → Prop) :
    ⟪fun s => ∀ x, v = some x → Q x s⟫ (assertOpt v) ⟪Q⟫ := by
  intro s hs r s' hr
  cases v with
  | none => exact hr.elim
  | some x => obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr; exact hs _ rfl

theorem select_wp (A : α → Prop) (Q : α → σ → Prop) :
    ⟪fun s => ∀ x, A x → Q x s⟫ (select A) ⟪Q⟫ := by
  intro s hs r s' ⟨hA, hs'⟩; cases hs'; exact hs r hA

theorem ite_wp (c : Prop) [Decidable c] {f g : NondetM σ α} {P₁ P₂ : σ → Prop} {Q : α → σ → Prop}
    (hf : ⟪P₁⟫ f ⟪Q⟫) (hg : ⟪P₂⟫ g ⟪Q⟫) :
    ⟪fun s => (c → P₁ s) ∧ (¬c → P₂ s)⟫ (if c then f else g) ⟪Q⟫ := by
  intro s hs r s' hr
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at hr; exact hf s (hs.1 hc) r s' hr
  · simp only [hc, ↓reduceIte] at hr; exact hg s (hs.2 hc) r s' hr

theorem whenM_wp (P : Prop) [Decidable P] (m : NondetM σ Unit) {R : σ → Prop} (Q : Unit → σ → Prop)
    (hm : ⟪R⟫ m ⟪Q⟫) : ⟪fun s => (P → R s) ∧ (¬P → Q () s)⟫ (whenM P m) ⟪Q⟫ := by
  intro s hs r s' hr
  unfold whenM at hr
  split at hr
  · rename_i hP; exact hm s (hs.1 hP) r s' hr
  · rename_i hP; cases hr; exact hs.2 hP

/-! ## no_fail rules -/

theorem noFail_ret (a : α) (P : σ → Prop) : noFail P (ret a : NondetM σ α) := fun _ _ h => h
theorem noFail_get (P : σ → Prop) : noFail P (get : NondetM σ σ) := fun _ _ h => h
theorem noFail_put (s₀ : σ) (P : σ → Prop) : noFail P (put s₀) := fun _ _ h => h

theorem noFail_bind {P Q : σ → Prop} {R : α → σ → Prop} {f : NondetM σ α} {g : α → NondetM σ β}
    (hf : noFail P f) (hg : ∀ x, noFail (R x) (g x)) (hv : ⟪Q⟫ f ⟪R⟫) :
    noFail (fun s => P s ∧ Q s) (bind f g) := by
  rintro s ⟨hP, hQ⟩ (⟨x, t, hx, hfail⟩ | hfail)
  · exact hg x t (hv s hQ x t hx) hfail
  · exact hf s hP hfail

/-! ## Tactics

`wp` applies wp rules backwards until no rule fits. `wpsimp` first opens the precondition
(`hoare_pre`), runs `wp`, then discharges the implication with `simp`.
These are deliberately simple; the real l4v `wp` has rule sets, combinators and `crunch` (walk stage).
-/

-- Rules apply under `with_reducible`: a rule fires only when the program's head matches syntactically.
-- Without this, `apply` unfolds `put`/`bind` (or searches `Decidable ?c` for `ite_wp`) and `repeat'` can spin.
macro "wp" : tactic => `(tactic| repeat' (first
  | (with_reducible apply bind_wp; intro)
  | (with_reducible apply bind_wp'; intro)
  | with_reducible apply ret_wp | with_reducible apply pure_wp
  | with_reducible apply get_wp | with_reducible apply put_wp
  | with_reducible apply gets_wp | with_reducible apply modify_wp
  | with_reducible apply fail_wp | with_reducible apply assertM_wp
  | with_reducible apply assertOpt_wp | with_reducible apply select_wp
  | with_reducible apply ite_wp))

macro "wpsimp" : tactic =>
  `(tactic| (apply hoare_pre; (focus wp); all_goals (try intro s hs); all_goals (try simp_all)))

end NondetM
end Sel4Lean
