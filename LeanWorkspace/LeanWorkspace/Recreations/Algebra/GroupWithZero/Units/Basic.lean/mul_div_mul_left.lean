import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b := hc.isUnit.mul_div_mul_left _ _

