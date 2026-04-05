import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_range_zero (f : ℕ → M) : ∏ k ∈ range 0, f k = 1 := by rw [range_zero, Finset.prod_empty]

