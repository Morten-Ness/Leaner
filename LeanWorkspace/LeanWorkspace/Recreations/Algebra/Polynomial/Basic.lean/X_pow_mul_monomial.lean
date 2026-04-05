import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_pow_mul_monomial (k n : ℕ) (r : R) : Polynomial.X ^ k * Polynomial.monomial n r = Polynomial.monomial (n + k) r := by
  rw [Polynomial.X_pow_mul, Polynomial.monomial_mul_X_pow]

