import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem TrailingMonic.def : Polynomial.TrailingMonic p ↔ Polynomial.trailingCoeff p = 1 := Iff.rfl

