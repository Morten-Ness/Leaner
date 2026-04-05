import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem star_mem {U : R} (hU : U ∈ unitary R) : star U ∈ unitary R := ⟨by rw [star_star, Unitary.mul_star_self_of_mem hU], by rw [star_star, Unitary.star_mul_self_of_mem hU]⟩

