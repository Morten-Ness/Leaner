import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem degree_C_le (a : R) : (Polynomial.C a).degree ≤ 0 := (le_of_eq (by rw [LaurentPolynomial.T_zero, mul_one])).trans (LaurentPolynomial.degree_C_mul_T_le 0 a)

