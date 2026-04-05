import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem card_eq_sum_ones (s : Finset ι) : #s = ∑ _ ∈ s, 1 := by simp

