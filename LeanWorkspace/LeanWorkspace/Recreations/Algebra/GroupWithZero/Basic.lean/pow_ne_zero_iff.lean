import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

variable [IsReduced M₀]

theorem pow_ne_zero_iff (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (pow_eq_zero_iff hn).not

