import Mathlib

variable {F α M N G : Type*}

variable [CommGroup G]

theorem symm_divLeft (a : G) : (Equiv.divLeft a).symm = Equiv.divLeft a := ext fun _ ↦ inv_mul_eq_div _ _

