import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem coe_mul_star_self (U : unitary R) : (U : R) * star U = 1 := Unitary.mul_star_self_of_mem U.prop

