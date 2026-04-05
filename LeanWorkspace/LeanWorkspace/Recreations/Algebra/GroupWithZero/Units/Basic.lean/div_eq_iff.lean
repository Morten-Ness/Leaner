import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b := hb.isUnit.div_eq_iff

