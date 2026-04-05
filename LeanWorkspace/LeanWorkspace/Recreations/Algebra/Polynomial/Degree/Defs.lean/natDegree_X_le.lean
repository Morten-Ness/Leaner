import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_X_le : (Polynomial.X : R[X]).natDegree ≤ 1 := natDegree_le_of_degree_le Polynomial.degree_X_le

