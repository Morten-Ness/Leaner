import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.swap_C (f : R[X]) : swap (C f) = f.map C := by
  simpa [← algebraMap_eq] using aeval_X_left_eq_map f

