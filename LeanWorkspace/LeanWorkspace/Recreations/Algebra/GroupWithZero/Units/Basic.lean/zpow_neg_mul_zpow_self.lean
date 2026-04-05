import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem zpow_neg_mul_zpow_self (n : ℤ) (ha : a ≠ 0) : a ^ (-n) * a ^ n = 1 := by
  rw [zpow_neg]; exact inv_mul_cancel₀ (zpow_ne_zero n ha)

