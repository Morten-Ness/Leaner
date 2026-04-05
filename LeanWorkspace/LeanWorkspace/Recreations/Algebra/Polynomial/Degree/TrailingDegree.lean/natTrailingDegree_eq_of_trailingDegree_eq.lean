import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]}
    (h : Polynomial.trailingDegree p = Polynomial.trailingDegree q) : Polynomial.natTrailingDegree p = Polynomial.natTrailingDegree q := by
  unfold Polynomial.natTrailingDegree
  rw [h]

