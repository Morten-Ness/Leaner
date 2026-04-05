import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem le_trailingDegree_X_pow (n : ℕ) : (n : ℕ∞) ≤ Polynomial.trailingDegree (Polynomial.X ^ n : R[X]) := by
  simpa only [C_1, one_mul] using Polynomial.le_trailingDegree_C_mul_X_pow n (1 : R)

