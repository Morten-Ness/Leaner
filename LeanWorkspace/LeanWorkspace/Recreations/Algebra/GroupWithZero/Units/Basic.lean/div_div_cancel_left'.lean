import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_div_cancel_left' (ha : a ≠ 0) : a / b / a = b⁻¹ := ha.isUnit.div_div_cancel_left

