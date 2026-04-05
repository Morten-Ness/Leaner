import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_monomial (ha : a ≠ 0) : Polynomial.natTrailingDegree (monomial n a) = n := by
  rw [Polynomial.natTrailingDegree, Polynomial.trailingDegree_monomial ha]
  rfl

