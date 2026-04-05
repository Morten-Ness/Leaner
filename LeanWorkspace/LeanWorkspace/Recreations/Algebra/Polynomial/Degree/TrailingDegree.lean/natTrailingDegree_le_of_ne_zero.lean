import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : Polynomial.natTrailingDegree p ≤ n := ENat.toNat_le_of_le_coe <| Polynomial.trailingDegree_le_of_ne_zero h

