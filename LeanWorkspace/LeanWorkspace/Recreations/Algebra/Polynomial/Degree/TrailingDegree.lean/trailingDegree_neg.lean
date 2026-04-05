import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Ring R]

theorem trailingDegree_neg (p : R[X]) : Polynomial.trailingDegree (-p) = Polynomial.trailingDegree p := by
  unfold Polynomial.trailingDegree
  rw [support_neg]

