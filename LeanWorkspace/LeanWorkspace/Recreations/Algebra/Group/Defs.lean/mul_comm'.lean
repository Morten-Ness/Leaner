import Mathlib

variable {G : Type*}

set_option backward.privateInPublic true in
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := left_inv_eq_right_inv (inv_mul_cancel a) h


theorem mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) : a * b = b * a := IsMulCommutative.is_comm.comm ..

