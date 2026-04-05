import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem star_mul_self_of_mem {U : R} (hU : U ∈ unitary R) : star U * U = 1 := hU.1

