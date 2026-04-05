import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b := hc.isUnit.mul_div_mul_right _ _

-- TODO: Duplicate of `mul_inv_cancel_right₀`

