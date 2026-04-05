import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_mul_monomial (n : ℕ) (r : R) : Polynomial.X * Polynomial.monomial n r = Polynomial.monomial (n + 1) r := by
  rw [Polynomial.X_mul, Polynomial.monomial_mul_X]

