import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem aevalAeval_C (x y : A) (p : R[X]) : (C p).aevalAeval x y = aeval x p := by simp

