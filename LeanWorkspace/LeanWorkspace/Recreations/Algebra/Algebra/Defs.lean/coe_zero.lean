import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem coe_zero : (↑(0 : R) : A) = 0 := map_zero (algebraMap R A)

