import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : ℕ}
    (h : Polynomial.trailingDegree p = n) : Polynomial.natTrailingDegree p = n := by
  simp [Polynomial.natTrailingDegree, h]

