import Mathlib

open scoped Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

theorem equivMvPolynomial_symm_C (a : R) : (Bivariate.equivMvPolynomial R).symm (.C a) = C (C a) := by
  simp [Bivariate.equivMvPolynomial]

