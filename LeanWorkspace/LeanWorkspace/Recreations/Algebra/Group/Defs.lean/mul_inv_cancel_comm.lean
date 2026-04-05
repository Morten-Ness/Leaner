import Mathlib

variable {G : Type*}

variable [CommGroup G]

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b := by rw [mul_comm, inv_mul_cancel_left]

