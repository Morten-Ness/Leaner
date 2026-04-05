import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroClass M₀] {a b : M₀}

theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

