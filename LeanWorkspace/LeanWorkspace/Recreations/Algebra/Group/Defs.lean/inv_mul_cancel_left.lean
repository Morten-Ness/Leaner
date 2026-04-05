import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

