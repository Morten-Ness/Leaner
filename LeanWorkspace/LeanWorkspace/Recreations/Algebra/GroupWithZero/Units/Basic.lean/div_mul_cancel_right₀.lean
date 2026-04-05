import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_mul_cancel_right₀ (hb : b ≠ 0) (a : G₀) : b / (a * b) = a⁻¹ := hb.isUnit.div_mul_cancel_right _

