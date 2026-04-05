import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem degree_T_le (n : ℤ) : (LaurentPolynomial.T n : R[T;T⁻¹]).degree ≤ n := (le_of_eq (by rw [map_one, one_mul])).trans (LaurentPolynomial.degree_C_mul_T_le n (1 : R))

