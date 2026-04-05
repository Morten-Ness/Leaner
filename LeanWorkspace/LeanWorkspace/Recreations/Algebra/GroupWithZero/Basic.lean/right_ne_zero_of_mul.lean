import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroClass M₀] {a b : M₀}

theorem right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 := mt (mul_eq_zero_of_right a)

