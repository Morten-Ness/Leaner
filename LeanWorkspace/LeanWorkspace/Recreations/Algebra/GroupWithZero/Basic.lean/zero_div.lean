import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem zero_div (a : G₀) : 0 / a = 0 := by rw [div_eq_mul_inv, zero_mul]

