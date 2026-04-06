import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem exists_ne_one_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by
  classical
  by_contra h'
  push_neg at h'
  apply h
  simpa [Finset.prod_const_one] using Finset.prod_congr rfl h'
