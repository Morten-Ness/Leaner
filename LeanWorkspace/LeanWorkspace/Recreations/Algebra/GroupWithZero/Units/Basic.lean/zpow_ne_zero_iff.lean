import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem zpow_ne_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (zpow_eq_zero_iff hn).ne

