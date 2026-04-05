import Mathlib

variable {G : Type*}

variable [DivInvMonoid G]

theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]

