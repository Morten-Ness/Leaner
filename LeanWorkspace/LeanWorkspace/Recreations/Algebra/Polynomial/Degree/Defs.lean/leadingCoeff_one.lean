import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_one : Polynomial.leadingCoeff (1 : R[X]) = 1 := Polynomial.leadingCoeff_C 1

