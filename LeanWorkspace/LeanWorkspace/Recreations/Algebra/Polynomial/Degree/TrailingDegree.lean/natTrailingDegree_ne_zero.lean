import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_ne_zero : Polynomial.natTrailingDegree p ≠ 0 ↔ p ≠ 0 ∧ coeff p 0 = 0 := natTrailingDegree_eq_zero.not.trans <| by rw [not_or, not_ne_iff]

