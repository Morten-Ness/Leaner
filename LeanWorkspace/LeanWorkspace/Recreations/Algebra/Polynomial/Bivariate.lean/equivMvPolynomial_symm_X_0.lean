import Mathlib

open scoped Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

theorem equivMvPolynomial_symm_X_0 : (Bivariate.equivMvPolynomial R).symm (.X 0) = C X := by
  simp [Bivariate.equivMvPolynomial]

