import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem monic_of_subsingleton [Subsingleton R] (p : R[X]) : Polynomial.Monic p := Subsingleton.elim _ _

