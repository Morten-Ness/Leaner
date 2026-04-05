import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

theorem pow_lt_pow_iff_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m := (pow_right_strictAnti₀ h₀ h₁).lt_iff_gt

