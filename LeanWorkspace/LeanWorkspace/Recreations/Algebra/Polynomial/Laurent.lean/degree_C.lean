import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem degree_C {a : R} (a0 : a ≠ 0) : (Polynomial.C a).degree = 0 := by
  rw [← mul_one (Polynomial.C a), ← LaurentPolynomial.T_zero]
  exact LaurentPolynomial.degree_C_mul_T 0 a a0

