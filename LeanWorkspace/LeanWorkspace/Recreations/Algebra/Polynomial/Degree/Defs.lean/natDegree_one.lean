import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_one : Polynomial.natDegree (1 : R[X]) = 0 := Polynomial.natDegree_C 1

