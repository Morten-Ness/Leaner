import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_eq_iff_natTrailingDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [Polynomial.trailingDegree_eq_natTrailingDegree hp, Nat.cast_inj]

