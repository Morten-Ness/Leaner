import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem T_add (m n : ℤ) : (LaurentPolynomial.T (m + n) : R[T;T⁻¹]) = LaurentPolynomial.T m * LaurentPolynomial.T n := by
  simp [LaurentPolynomial.T, single_mul_single]

