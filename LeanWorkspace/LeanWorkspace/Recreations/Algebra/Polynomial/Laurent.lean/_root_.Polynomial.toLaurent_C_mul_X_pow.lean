import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_C_mul_X_pow (n : ℕ) (r : R) :
    toLaurent (Polynomial.C r * Polynomial.X ^ n) = Polynomial.C r * LaurentPolynomial.T n := by
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]

