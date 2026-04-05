import Mathlib

variable {G : Type*}

variable [DivInvMonoid G]

theorem one_div (a : G) : 1 / a = a⁻¹ := (inv_eq_one_div a).symm

