import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem aevalAeval_X (x y : A) : (C X : R[X][Y]).aevalAeval x y = x := by rw [aevalAeval_C, aeval_X]

