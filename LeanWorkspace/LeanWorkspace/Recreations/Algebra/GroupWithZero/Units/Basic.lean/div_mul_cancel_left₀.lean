import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_mul_cancel_left₀ (ha : a ≠ 0) (b : G₀) : a / (a * b) = b⁻¹ := ha.isUnit.div_mul_cancel_left _

