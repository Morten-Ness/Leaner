import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_pow_mul_assoc {n : ℕ} : p * Polynomial.X ^ n * q = p * q * Polynomial.X ^ n := by
  rw [mul_assoc, Polynomial.X_pow_mul, ← mul_assoc]

