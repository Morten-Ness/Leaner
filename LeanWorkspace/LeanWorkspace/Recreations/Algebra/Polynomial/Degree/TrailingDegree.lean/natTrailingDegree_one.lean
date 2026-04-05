import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natTrailingDegree_one : Polynomial.natTrailingDegree (1 : R[X]) = 0 := Polynomial.natTrailingDegree_C 1

