import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

variable [IsReduced M₀]

theorem sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0 := pow_eq_zero_iff two_ne_zero

