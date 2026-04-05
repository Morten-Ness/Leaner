import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem T_sub (m n : ℤ) : (LaurentPolynomial.T (m - n) : R[T;T⁻¹]) = LaurentPolynomial.T m * LaurentPolynomial.T (-n) := by rw [← LaurentPolynomial.T_add, sub_eq_add_neg]

