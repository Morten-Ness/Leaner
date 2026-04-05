import Mathlib

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = (a : A) ^ n := map_pow (algebraMap R A) _ _

