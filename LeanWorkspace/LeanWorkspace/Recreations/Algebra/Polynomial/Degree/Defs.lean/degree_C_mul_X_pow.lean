import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : Polynomial.degree (Polynomial.C a * Polynomial.X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, Polynomial.degree_monomial n ha]

