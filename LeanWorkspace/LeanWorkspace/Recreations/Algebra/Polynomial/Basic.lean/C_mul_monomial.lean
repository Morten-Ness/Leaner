import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_mul_monomial : Polynomial.C a * Polynomial.monomial n b = Polynomial.monomial n (a * b) := by
  simp only [← Polynomial.monomial_zero_left, Polynomial.monomial_mul_monomial, zero_add]

