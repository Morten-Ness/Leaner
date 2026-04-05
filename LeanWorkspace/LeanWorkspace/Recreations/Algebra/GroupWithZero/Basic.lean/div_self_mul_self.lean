import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_cancel a]

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

