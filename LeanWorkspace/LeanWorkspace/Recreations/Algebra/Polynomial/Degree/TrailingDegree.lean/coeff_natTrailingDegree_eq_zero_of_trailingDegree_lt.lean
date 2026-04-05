import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
    (h : Polynomial.trailingDegree p < Polynomial.trailingDegree q) : coeff q (Polynomial.natTrailingDegree p) = 0 := Polynomial.coeff_eq_zero_of_lt_trailingDegree <| Polynomial.natTrailingDegree_le_trailingDegree.trans_lt h

