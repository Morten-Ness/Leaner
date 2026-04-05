import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.swap_swap_apply (p : R[X][Y]) : swap (swap p) = p := AlgEquiv.symm_apply_apply swap p

