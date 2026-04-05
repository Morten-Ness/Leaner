import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem mul_star_self (U : unitary R) : U * star U = 1 := Subtype.ext <| Unitary.coe_mul_star_self U

