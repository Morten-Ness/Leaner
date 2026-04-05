import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem zpow_sub₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m - n) = a ^ m / a ^ n := by
  rw [Int.sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]

