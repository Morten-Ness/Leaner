import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem mul_div_cancel₀ (a : G₀) (hb : b ≠ 0) : b * (a / b) = a := hb.isUnit.mul_div_cancel _

