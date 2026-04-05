import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem degree_C_ite [DecidableEq R] (a : R) : (Polynomial.C a).degree = if a = 0 then ⊥ else 0 := by
  split_ifs with h <;> simp only [h, map_zero, LaurentPolynomial.degree_zero, LaurentPolynomial.degree_C, Ne, not_false_iff]

