import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_X_pow_le (n : ℕ) : Polynomial.degree (Polynomial.X ^ n : R[X]) ≤ n := by
  simpa only [C_1, one_mul] using Polynomial.degree_C_mul_X_pow_le n (1 : R)

