import Mathlib

open scoped Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

theorem equivMvPolynomial_symm_X_1 : (Bivariate.equivMvPolynomial R).symm (.X 1) = X := by
  simp [Bivariate.equivMvPolynomial]

