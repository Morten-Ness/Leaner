import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem zpow_ne_zero {a : G₀} : ∀ n : ℤ, a ≠ 0 → a ^ n ≠ 0
  | (_ : ℕ) => by rw [zpow_natCast]; exact pow_ne_zero _
  | .negSucc n => fun ha ↦ by rw [zpow_negSucc]; exact inv_ne_zero (pow_ne_zero _ ha)
