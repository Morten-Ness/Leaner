import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_range_one (f : ℕ → M) : ∏ k ∈ range 1, f k = f 0 := by
  rw [range_one, Finset.prod_singleton]

