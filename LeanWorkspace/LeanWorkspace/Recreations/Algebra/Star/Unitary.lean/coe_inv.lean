import Mathlib

variable {R : Type*}

variable [GroupWithZero R] [StarMul R]

theorem coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R) := eq_inv_of_mul_eq_one_right <| Unitary.coe_mul_star_self _

