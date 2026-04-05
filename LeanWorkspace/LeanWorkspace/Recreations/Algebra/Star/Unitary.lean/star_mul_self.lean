import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem star_mul_self (U : unitary R) : star U * U = 1 := Subtype.ext <| Unitary.coe_star_mul_self U

