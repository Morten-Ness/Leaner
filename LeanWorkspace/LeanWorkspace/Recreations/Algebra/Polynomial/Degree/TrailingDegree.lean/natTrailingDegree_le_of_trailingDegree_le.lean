import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_le_of_trailingDegree_le {n : ℕ} {hp : p ≠ 0}
    (H : (n : ℕ∞) ≤ Polynomial.trailingDegree p) : n ≤ Polynomial.natTrailingDegree p := by
  rwa [Polynomial.trailingDegree_eq_natTrailingDegree hp, Nat.cast_le] at H

