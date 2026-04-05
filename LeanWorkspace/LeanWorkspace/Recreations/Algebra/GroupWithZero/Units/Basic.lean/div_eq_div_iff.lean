import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b := hb.isUnit.div_eq_div_iff hd.isUnit

