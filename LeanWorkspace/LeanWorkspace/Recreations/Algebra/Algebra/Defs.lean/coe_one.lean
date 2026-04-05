import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem coe_one : (↑(1 : R) : A) = 1 := map_one (algebraMap R A)

