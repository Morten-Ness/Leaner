import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_monomial (ha : a ≠ 0) : Polynomial.trailingDegree (monomial n a) = n := by
  rw [Polynomial.trailingDegree, support_monomial n ha, min_singleton]
  rfl

