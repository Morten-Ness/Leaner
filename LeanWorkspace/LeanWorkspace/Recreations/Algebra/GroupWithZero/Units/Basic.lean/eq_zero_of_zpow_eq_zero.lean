import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem eq_zero_of_zpow_eq_zero {n : ℤ} : a ^ n = 0 → a = 0 := not_imp_not.1 (zpow_ne_zero _)

