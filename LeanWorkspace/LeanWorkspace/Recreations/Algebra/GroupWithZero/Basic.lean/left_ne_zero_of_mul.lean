import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroClass M₀] {a b : M₀}

theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 := mt fun h => mul_eq_zero_of_left h b

