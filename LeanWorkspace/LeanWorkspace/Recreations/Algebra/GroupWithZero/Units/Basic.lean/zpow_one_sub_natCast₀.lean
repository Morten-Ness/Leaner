import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem zpow_one_sub_natCast₀ (ha : a ≠ 0) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  simpa using zpow_sub₀ ha 1 n

