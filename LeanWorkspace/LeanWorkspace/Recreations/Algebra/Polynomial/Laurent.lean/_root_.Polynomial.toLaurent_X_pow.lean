import Mathlib

open scoped Polynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_X_pow (n : ℕ) : toLaurent (Polynomial.X ^ n : R[X]) = LaurentPolynomial.T n := by
  simp only [map_pow, Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_one]

