import Mathlib

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) := map_div₀ (algebraMap R A) r s

