import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 := right_ne_zero_of_mul <| ne_zero_of_eq_one h

