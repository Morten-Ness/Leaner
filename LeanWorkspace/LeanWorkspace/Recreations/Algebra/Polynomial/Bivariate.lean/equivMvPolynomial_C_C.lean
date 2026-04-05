import Mathlib

open scoped Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

theorem equivMvPolynomial_C_C {a} : Bivariate.equivMvPolynomial R (C (C a)) = .C a := by
  simp [Bivariate.equivMvPolynomial]

