import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_C (a : R) : Polynomial.leadingCoeff (Polynomial.C a) = a := Polynomial.leadingCoeff_monomial a 0

