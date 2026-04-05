import Mathlib

open scoped Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

theorem pderiv_zero_equivMvPolynomial {R : Type*} [CommRing R] (p : R[X][Y]) :
    (Bivariate.equivMvPolynomial R p).pderiv 0 = Bivariate.equivMvPolynomial R
      (PolynomialModule.equivPolynomialSelf (derivative'.mapCoeffs p)) := by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [map_nsmul]

