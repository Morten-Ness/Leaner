import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_C (r : R) : toLaurent (Polynomial.C r) = Polynomial.C r := by
  convert Polynomial.toLaurent_C_mul_T 0 r
  simp only [Int.ofNat_zero, LaurentPolynomial.T_zero, mul_one]

