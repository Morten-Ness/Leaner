import Mathlib

open scoped Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

theorem equivMvPolynomial_C_X : Bivariate.equivMvPolynomial R (C X) = .X 0 := by
  simp [Bivariate.equivMvPolynomial]

