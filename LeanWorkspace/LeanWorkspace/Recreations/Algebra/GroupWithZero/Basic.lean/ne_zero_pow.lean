import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem ne_zero_pow (hn : n ≠ 0) (ha : a ^ n ≠ 0) : a ≠ 0 := by rintro rfl; exact ha <| zero_pow hn

