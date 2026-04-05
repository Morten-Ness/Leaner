import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c := hb.isUnit.div_eq_of_eq_mul

