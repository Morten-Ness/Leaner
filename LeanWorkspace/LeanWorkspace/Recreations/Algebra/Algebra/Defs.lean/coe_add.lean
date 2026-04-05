import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b := map_add (algebraMap R A) a b

