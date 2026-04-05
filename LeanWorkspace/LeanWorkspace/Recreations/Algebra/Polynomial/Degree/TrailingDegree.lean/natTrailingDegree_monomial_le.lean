import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_monomial_le : Polynomial.natTrailingDegree (monomial n a) ≤ n := letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (Polynomial.natTrailingDegree_monomial ha).le

