import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem monomial_mul_X (n : ℕ) (r : R) : Polynomial.monomial n r * Polynomial.X = Polynomial.monomial (n + 1) r := by
  rw [Polynomial.X, Polynomial.monomial_mul_monomial, mul_one]

