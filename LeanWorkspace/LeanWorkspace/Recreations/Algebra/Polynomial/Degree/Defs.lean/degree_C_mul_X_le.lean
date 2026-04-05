import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_C_mul_X_le (a : R) : Polynomial.degree (Polynomial.C a * Polynomial.X) ≤ 1 := by
  simpa only [pow_one] using Polynomial.degree_C_mul_X_pow_le 1 a

