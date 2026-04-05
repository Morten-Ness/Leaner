import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subtype_of_mem (f : ι → M) {p : ι → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s, f x := by
  rw [Finset.prod_subtype_eq_prod_filter, filter_true_of_mem]
  simpa using h

