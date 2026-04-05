import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem IsUnit.prod_univ_iff [Fintype ι] [CommMonoid M] {f : ι → M} :
    IsUnit (∏ a, f a) ↔ ∀ a, IsUnit (f a) := by simp

