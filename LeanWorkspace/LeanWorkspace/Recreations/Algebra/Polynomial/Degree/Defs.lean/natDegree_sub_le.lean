import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_sub_le (p q : R[X]) : Polynomial.natDegree (p - q) ≤ max (Polynomial.natDegree p) (Polynomial.natDegree q) := by
  simpa only [← Polynomial.natDegree_neg q] using Polynomial.natDegree_add_le p (-q)

