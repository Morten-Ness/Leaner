import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_C_mul_X_pow_le (n : ℕ) (a : R) : Polynomial.degree (Polynomial.C a * Polynomial.X ^ n) ≤ n := by
  rw [C_mul_X_pow_eq_monomial]
  apply Polynomial.degree_monomial_le

