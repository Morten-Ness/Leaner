import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_one_le : (0 : ℕ∞) ≤ Polynomial.trailingDegree (1 : R[X]) := by
  rw [← C_1]
  exact Polynomial.le_trailingDegree_C

