import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a := hb.isUnit.eq_div_iff

-- TODO: Swap RHS around

