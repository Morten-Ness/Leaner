import Mathlib

variable {M₀ G₀ : Type*}

variable [CommGroupWithZero G₀]

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [sq, mul_assoc, mul_div_cancel_left₀ _ ha]

