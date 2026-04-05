import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem mul_star_self_of_mem {U : R} (hU : U ∈ unitary R) : U * star U = 1 := hU.2

