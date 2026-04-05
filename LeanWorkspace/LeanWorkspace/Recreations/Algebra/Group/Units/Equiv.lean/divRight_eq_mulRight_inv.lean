import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ := ext fun _ => div_eq_mul_inv _ _

