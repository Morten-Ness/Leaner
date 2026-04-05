import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a := div_eq_iff hb.isUnit.trans eq_comm

