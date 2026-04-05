import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

variable [IsReduced M₀]

theorem pow_ne_zero (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 := mt eq_zero_of_pow_eq_zero h

