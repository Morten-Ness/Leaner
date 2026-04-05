import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b := eq_div_iff hc.isUnit

