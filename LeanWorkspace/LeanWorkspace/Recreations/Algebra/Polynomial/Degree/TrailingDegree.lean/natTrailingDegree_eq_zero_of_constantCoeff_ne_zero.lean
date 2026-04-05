import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]}

theorem natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (h : constantCoeff p ≠ 0) :
    p.natTrailingDegree = 0 := le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero h) zero_le'

