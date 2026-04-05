import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b := hb.isUnit.div_eq_one_iff_eq

