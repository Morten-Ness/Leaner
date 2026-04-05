import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 := Unitary.star_mul_self_of_mem U.prop

