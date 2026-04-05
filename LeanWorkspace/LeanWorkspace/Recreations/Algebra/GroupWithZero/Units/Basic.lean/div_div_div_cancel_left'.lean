import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_div_div_cancel_left' (a b : G₀) (hc : c ≠ 0) : c / a / (c / b) = b / a := by
  rw [div_div_div_eq, mul_comm, mul_div_mul_right _ _ hc]

