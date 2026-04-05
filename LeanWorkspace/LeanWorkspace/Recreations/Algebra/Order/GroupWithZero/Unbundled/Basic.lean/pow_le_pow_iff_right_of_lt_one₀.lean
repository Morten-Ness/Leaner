import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

theorem pow_le_pow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ m ≤ a ^ n ↔ n ≤ m := (pow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

