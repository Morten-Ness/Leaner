import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_X : (toLaurent Polynomial.X : R[T;T⁻¹]) = LaurentPolynomial.T 1 := by
  have : (Polynomial.X : R[X]) = monomial 1 1 := by simp [← C_mul_X_pow_eq_monomial]
  simp [this, Polynomial.toLaurent_C_mul_T]

