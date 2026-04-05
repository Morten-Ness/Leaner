import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b := map_mul (algebraMap R A) a b

