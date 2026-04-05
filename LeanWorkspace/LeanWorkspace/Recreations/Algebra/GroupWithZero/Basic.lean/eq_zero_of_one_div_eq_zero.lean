import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 := Classical.byCases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim

