import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_X_le : (Polynomial.X : R[X]).natTrailingDegree ≤ 1 := Polynomial.natTrailingDegree_monomial_le

