import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem degree_C_mul_T_le (n : ℤ) (a : R) : LaurentPolynomial.degree (Polynomial.C a * LaurentPolynomial.T n) ≤ n := by
  by_cases a0 : a = 0
  · simp only [a0, map_zero, zero_mul, LaurentPolynomial.degree_zero, bot_le]
  · exact (LaurentPolynomial.degree_C_mul_T n a a0).le

