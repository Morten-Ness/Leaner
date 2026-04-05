import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem mul_inv_mul_cancel (a : G₀) : a * a⁻¹ * a = a := by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel₀ h, one_mul]

