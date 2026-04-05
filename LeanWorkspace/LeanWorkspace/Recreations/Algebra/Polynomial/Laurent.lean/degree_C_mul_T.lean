import Mathlib

variable {R S : Type*}

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
theorem degree_C_mul_T (n : ℤ) (a : R) (a0 : a ≠ 0) : LaurentPolynomial.degree (Polynomial.C a * LaurentPolynomial.T n) = n := by
  rw [LaurentPolynomial.degree, LaurentPolynomial.support_C_mul_T_of_ne_zero a0 n]
  exact Finset.max_singleton

