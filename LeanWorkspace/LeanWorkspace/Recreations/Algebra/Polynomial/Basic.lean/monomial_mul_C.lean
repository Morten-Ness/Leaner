import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_mul_C : Polynomial.monomial n a * Polynomial.C b = Polynomial.monomial n (a * b) := by
  simp only [← Polynomial.monomial_zero_left, Polynomial.monomial_mul_monomial, add_zero]

