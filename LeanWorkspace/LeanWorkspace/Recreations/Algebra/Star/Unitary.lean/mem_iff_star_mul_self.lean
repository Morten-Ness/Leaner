import Mathlib

variable {R : Type*}

variable [CommMonoid R] [StarMul R]

theorem mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 := Unitary.mem_iff.trans <| and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h

