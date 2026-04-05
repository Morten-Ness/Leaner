import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : Polynomial.trailingDegree p ≤ n := min_le (mem_support_iff.2 h)

