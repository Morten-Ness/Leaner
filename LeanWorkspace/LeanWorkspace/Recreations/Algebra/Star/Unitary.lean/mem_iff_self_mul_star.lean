import Mathlib

variable {R : Type*}

variable [CommMonoid R] [StarMul R]

theorem mem_iff_self_mul_star {U : R} : U ∈ unitary R ↔ U * star U = 1 := Unitary.mem_iff.trans <| and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h

