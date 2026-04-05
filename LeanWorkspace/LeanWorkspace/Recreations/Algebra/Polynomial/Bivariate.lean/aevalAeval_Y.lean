import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem aevalAeval_Y (x y : A) : (Y : R[X][Y]).aevalAeval x y = y := by simp

