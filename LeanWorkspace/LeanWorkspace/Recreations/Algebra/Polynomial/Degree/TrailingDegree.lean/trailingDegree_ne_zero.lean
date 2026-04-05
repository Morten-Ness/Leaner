import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_ne_zero : Polynomial.trailingDegree p ≠ 0 ↔ coeff p 0 = 0 := Polynomial.trailingDegree_eq_zero.not_left

