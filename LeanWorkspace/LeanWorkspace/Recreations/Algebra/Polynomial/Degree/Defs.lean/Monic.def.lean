import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem Monic.def : Polynomial.Monic p ↔ Polynomial.leadingCoeff p = 1 := Iff.rfl

