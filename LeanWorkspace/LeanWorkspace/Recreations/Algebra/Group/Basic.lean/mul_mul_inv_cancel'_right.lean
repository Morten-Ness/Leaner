import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel a b]

