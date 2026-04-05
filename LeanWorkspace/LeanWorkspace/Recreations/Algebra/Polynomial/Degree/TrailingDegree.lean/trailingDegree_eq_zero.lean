import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_eq_zero : Polynomial.trailingDegree p = 0 ↔ coeff p 0 ≠ 0 := Finset.min_eq_bot.trans mem_support_iff

