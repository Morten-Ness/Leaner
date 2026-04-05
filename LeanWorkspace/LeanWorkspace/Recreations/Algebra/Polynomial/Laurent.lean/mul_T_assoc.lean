import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem mul_T_assoc (f : R[T;T⁻¹]) (m n : ℤ) : f * LaurentPolynomial.T m * LaurentPolynomial.T n = f * LaurentPolynomial.T (m + n) := by
  simp [← LaurentPolynomial.T_add, mul_assoc]

