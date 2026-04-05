import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem IsUnit.prod_iff [CommMonoid M] {f : ι → M} :
    IsUnit (∏ a ∈ s, f a) ↔ ∀ a ∈ s, IsUnit (f a) := by
  induction s using Finset.cons_induction with grind

