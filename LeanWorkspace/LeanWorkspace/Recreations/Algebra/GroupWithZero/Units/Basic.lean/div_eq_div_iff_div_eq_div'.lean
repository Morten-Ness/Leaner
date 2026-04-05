import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_eq_div_iff_div_eq_div' (hb : b ≠ 0) (hc : c ≠ 0) : a / b = c / d ↔ a / c = b / d := by
  conv_lhs => rw [← mul_left_inj' hb, div_mul_cancel₀ _ hb]
  conv_rhs => rw [← mul_left_inj' hc, div_mul_cancel₀ _ hc]
  rw [mul_comm _ c, div_mul_eq_mul_div, mul_div_assoc]

