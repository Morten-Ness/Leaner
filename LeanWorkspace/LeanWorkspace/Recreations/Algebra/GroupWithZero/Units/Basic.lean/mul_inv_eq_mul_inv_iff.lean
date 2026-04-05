import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem mul_inv_eq_mul_inv_iff (hb : b ≠ 0) (hd : d ≠ 0) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := hb.isUnit.mul_inv_eq_mul_inv_iff hd.isUnit

