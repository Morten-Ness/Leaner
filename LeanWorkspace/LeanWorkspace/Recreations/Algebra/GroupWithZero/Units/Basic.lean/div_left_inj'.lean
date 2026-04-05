import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b := hc.isUnit.div_left_inj

