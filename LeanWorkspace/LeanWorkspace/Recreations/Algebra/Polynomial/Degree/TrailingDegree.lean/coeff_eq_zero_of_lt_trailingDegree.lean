import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_eq_zero_of_lt_trailingDegree (h : (n : ℕ∞) < Polynomial.trailingDegree p) : coeff p n = 0 := Classical.not_not.1 (mt Polynomial.trailingDegree_le_of_ne_zero (not_le_of_gt h))

