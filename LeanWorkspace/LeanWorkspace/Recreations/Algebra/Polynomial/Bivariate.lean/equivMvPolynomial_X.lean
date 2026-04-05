import Mathlib

open scoped Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

theorem equivMvPolynomial_X : Bivariate.equivMvPolynomial R X = .X 1 := by
  simp [Bivariate.equivMvPolynomial]

