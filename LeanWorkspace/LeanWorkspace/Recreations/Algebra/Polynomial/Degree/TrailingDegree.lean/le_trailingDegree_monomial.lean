import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem le_trailingDegree_monomial : ↑n ≤ Polynomial.trailingDegree (monomial n a) := letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (Polynomial.trailingDegree_monomial ha).ge

