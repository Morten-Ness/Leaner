import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.swap_C_C (r : R) : swap (C (C r)) = C (C r) := by simp

