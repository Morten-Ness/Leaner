import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_eq_iff_natTrailingDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : n ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [Polynomial.natTrailingDegree, ENat.toNat_eq_iff hn]

