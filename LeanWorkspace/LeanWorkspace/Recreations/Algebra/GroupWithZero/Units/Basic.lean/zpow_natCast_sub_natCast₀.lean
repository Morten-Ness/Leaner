import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem zpow_natCast_sub_natCast₀ (ha : a ≠ 0) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  simpa using zpow_sub₀ ha m n

