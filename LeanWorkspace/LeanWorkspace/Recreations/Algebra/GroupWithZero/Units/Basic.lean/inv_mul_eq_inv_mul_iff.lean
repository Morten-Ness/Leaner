import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem inv_mul_eq_inv_mul_iff (hb : b ≠ 0) (hd : d ≠ 0) :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := hb.isUnit.inv_mul_eq_inv_mul_iff hd.isUnit

