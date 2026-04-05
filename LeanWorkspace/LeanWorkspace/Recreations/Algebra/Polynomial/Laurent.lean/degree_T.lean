import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem degree_T [Nontrivial R] (n : ℤ) : (LaurentPolynomial.T n : R[T;T⁻¹]).degree = n := by
  rw [← one_mul (LaurentPolynomial.T n), ← map_one Polynomial.C]
  exact LaurentPolynomial.degree_C_mul_T n 1 (one_ne_zero : (1 : R) ≠ 0)

