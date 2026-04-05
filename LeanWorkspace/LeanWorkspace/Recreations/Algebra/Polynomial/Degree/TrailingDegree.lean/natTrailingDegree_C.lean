import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_C (a : R) : Polynomial.natTrailingDegree (Polynomial.C a) = 0 := nonpos_iff_eq_zero.1 Polynomial.natTrailingDegree_monomial_le

