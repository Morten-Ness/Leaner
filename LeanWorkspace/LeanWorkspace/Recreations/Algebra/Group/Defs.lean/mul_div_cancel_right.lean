import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem mul_div_cancel_right (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv, mul_inv_cancel_right a b]

