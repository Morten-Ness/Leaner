import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem T_pow (m : ℤ) (n : ℕ) : (LaurentPolynomial.T m ^ n : R[T;T⁻¹]) = LaurentPolynomial.T (n * m) := by
  rw [LaurentPolynomial.T, LaurentPolynomial.T, single_pow, one_pow, nsmul_eq_mul]

