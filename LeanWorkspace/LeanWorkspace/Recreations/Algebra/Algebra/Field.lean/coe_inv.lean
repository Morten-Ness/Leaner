import Mathlib

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) := map_inv₀ (algebraMap R A) r

