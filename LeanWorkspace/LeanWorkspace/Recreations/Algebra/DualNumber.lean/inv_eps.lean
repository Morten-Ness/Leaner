import Mathlib

variable {R A B : Type*}

theorem inv_eps [DivisionRing R] : (ε : R[ε])⁻¹ = 0 := TrivSqZeroExt.inv_inr 1

