import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : Polynomial.trailingDegree (Polynomial.C a * Polynomial.X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, Polynomial.trailingDegree_monomial ha]

