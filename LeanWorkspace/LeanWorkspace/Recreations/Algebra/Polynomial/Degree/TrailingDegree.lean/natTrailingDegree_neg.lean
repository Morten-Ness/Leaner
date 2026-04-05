import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Ring R]

theorem natTrailingDegree_neg (p : R[X]) : Polynomial.natTrailingDegree (-p) = Polynomial.natTrailingDegree p := by
  simp [Polynomial.natTrailingDegree]

