import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem zpow_natCast_sub_one₀ (ha : a ≠ 0) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa using zpow_sub₀ ha n 1

