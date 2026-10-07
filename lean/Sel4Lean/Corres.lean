import Sel4Lean.Monad.VCG

/-!
# Refinement: `corres`

Port of l4v `lib/Corres_UL.thy` (core):

```
corres_underlying srel nf nf' rrel G G' ≡ λm m'.
  ∀(s, s') ∈ srel. G s ∧ G' s' ⟶
    (nf ⟶ ¬ snd (m s)) ⟶
    (∀(r', t') ∈ fst (m' s'). ∃(r, t) ∈ fst (m s). (t, t') ∈ srel ∧ rrel r r') ∧
    (nf' ⟶ ¬ snd (m' s'))
```

Read: from related states satisfying the guards, every concrete outcome is matched by some abstract
outcome, with related final states and related return values. With `nf'`, the concrete side does not
fail. `srel` is a relation `σ → τ → Prop` here, where l4v uses a set of pairs.
-/

namespace Sel4Lean
open NondetM

variable {σ τ α β γ δ : Type}

/-- l4v `corres_underlying srel nf nf' rrel G G' m m'` -/
def corresUnderlying (srel : σ → τ → Prop) (nf nf' : Prop) (rrel : α → β → Prop)
    (G : σ → Prop) (G' : τ → Prop) (m : NondetM σ α) (m' : NondetM τ β) : Prop :=
  ∀ s s', srel s s' → G s → G' s' → (nf → ¬ (m s).2) →
    (∀ r' t', (m' s').1 (r', t') → ∃ r t, (m s).1 (r, t) ∧ srel t t' ∧ rrel r r') ∧
    (nf' → ¬ (m' s').2)

/-- l4v `corres_guard_imp`: strengthen both guards. -/
theorem corres_guard_imp {srel : σ → τ → Prop} {nf nf' : Prop} {rrel : α → β → Prop}
    {Q P : σ → Prop} {Q' P' : τ → Prop} {f : NondetM σ α} {g : NondetM τ β}
    (h : corresUnderlying srel nf nf' rrel Q Q' f g)
    (hP : ∀ s, P s → Q s) (hP' : ∀ s, P' s → Q' s) :
    corresUnderlying srel nf nf' rrel P P' f g :=
  fun s s' hs hG hG' hnf => h s s' hs (hP s hG) (hP' s' hG') hnf

/-- l4v `corres_return` (the useful direction). -/
theorem corres_return {srel : σ → τ → Prop} {nf nf' : Prop} {rrel : α → β → Prop}
    {P : σ → Prop} {P' : τ → Prop} {a : α} {b : β} (hab : rrel a b) :
    corresUnderlying srel nf nf' rrel P P' (ret a) (ret b) := by
  intro s s' hs _ _ _
  refine ⟨?_, fun _ h => h⟩
  intro r' t' h
  cases h
  exact ⟨a, s, rfl, hs, hab⟩

/-- `get` on both sides returns the related states themselves. -/
theorem corres_get {srel : σ → τ → Prop} {nf nf' : Prop} {P : σ → Prop} {P' : τ → Prop} :
    corresUnderlying srel nf nf' srel P P' get get := by
  intro s s' hs _ _ _
  refine ⟨?_, fun _ h => h⟩
  intro r' t' h
  cases h
  exact ⟨s, s, rfl, hs, hs⟩

/-- `put` of related states. -/
theorem corres_put {srel : σ → τ → Prop} {nf nf' : Prop} {P : σ → Prop} {P' : τ → Prop}
    {t : σ} {t' : τ} (ht : srel t t') :
    corresUnderlying srel nf nf' (fun _ _ => True) P P' (put t) (put t') := by
  intro s s' _ _ _ _
  refine ⟨?_, fun _ h => h⟩
  intro r' u h
  cases h
  exact ⟨(), t, rfl, ht, trivial⟩

/-- l4v `corres_split`: refine a bind by refining both halves.
`R`/`R'` are what each side establishes for the continuation (proved with `wp`). -/
theorem corres_split {srel : σ → τ → Prop} {nf nf' : Prop}
    {r' : α → β → Prop} {r : γ → δ → Prop}
    {P Q : σ → Prop} {P' Q' : τ → Prop} {R : α → σ → Prop} {R' : β → τ → Prop}
    {a : NondetM σ α} {c : NondetM τ β} {b : α → NondetM σ γ} {d : β → NondetM τ δ}
    (hx : corresUnderlying srel nf nf' r' P P' a c)
    (hy : ∀ rv rv', r' rv rv' → corresUnderlying srel nf nf' r (R rv) (R' rv') (b rv) (d rv'))
    (ha : ⟪Q⟫ a ⟪R⟫) (hc : ⟪Q'⟫ c ⟪R'⟫) :
    corresUnderlying srel nf nf' r (fun s => P s ∧ Q s) (fun s => P' s ∧ Q' s)
      (a >>= b) (c >>= d) := by
  intro s s' hs ⟨hP, hQ⟩ ⟨hP', hQ'⟩ hnf
  -- the first halves correspond; `a` cannot fail because `a >>= b` cannot
  obtain ⟨hres, hnfc⟩ := hx s s' hs hP hP' (fun h hfail => hnf h (Or.inr hfail))
  -- for each concrete intermediate outcome, find its abstract partner and use the continuation
  have step : ∀ rv' u', (c s').1 (rv', u') → ∃ rv u, (a s).1 (rv, u) ∧
      ((∀ x' t', (d rv' u').1 (x', t') → ∃ x t, (b rv u).1 (x, t) ∧ srel t t' ∧ r x x') ∧
       (nf' → ¬ (d rv' u').2)) := by
    intro rv' u' hcu
    obtain ⟨rv, u, hau, hsu, hr⟩ := hres rv' u' hcu
    exact ⟨rv, u, hau, hy rv rv' hr u u' hsu (ha s hQ rv u hau) (hc s' hQ' rv' u' hcu)
      (fun h hfail => hnf h (Or.inl ⟨rv, u, hau, hfail⟩))⟩
  refine ⟨?_, ?_⟩
  · rintro x' t' ⟨rv', u', hcu, hdu⟩
    obtain ⟨rv, u, hau, hcont, _⟩ := step rv' u' hcu
    obtain ⟨x, t, hbu, hst, hrx⟩ := hcont x' t' hdu
    exact ⟨x, t, ⟨rv, u, hau, hbu⟩, hst, hrx⟩
  · rintro hnf' (⟨rv', u', hcu, hdfail⟩ | hcfail)
    · obtain ⟨_, _, _, _, hnfd⟩ := step rv' u' hcu
      exact hnfd hnf' hdfail
    · exact hnfc hnf' hcfail

/-- Anything satisfies the trivial postcondition. -/
theorem valid_true {P : σ → Prop} {f : NondetM σ α} : ⟪P⟫ f ⟪fun _ _ => True⟫ :=
  fun _ _ _ _ _ => trivial

end Sel4Lean
