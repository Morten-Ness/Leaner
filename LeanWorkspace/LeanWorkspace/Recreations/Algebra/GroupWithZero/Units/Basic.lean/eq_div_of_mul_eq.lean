import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c := hc.isUnit.eq_div_of_mul_eq

