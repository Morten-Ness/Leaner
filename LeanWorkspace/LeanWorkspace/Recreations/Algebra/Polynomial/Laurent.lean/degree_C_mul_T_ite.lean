import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem degree_C_mul_T_ite [DecidableEq R] (n : ℤ) (a : R) :
    LaurentPolynomial.degree (Polynomial.C a * LaurentPolynomial.T n) = if a = 0 then ⊥ else ↑n := by
  split_ifs with h <;>
    simp only [h, map_zero, zero_mul, LaurentPolynomial.degree_zero, LaurentPolynomial.degree_C_mul_T, Ne,
      not_false_iff]

