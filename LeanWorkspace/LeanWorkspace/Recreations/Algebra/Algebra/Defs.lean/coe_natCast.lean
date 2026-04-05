import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem coe_natCast (a : ℕ) : (↑(a : R) : A) = a := map_natCast (algebraMap R A) a

