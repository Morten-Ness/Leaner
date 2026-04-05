import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]


theorem zpow_sub_one₀ (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ := calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, Int.sub_add_cancel]

