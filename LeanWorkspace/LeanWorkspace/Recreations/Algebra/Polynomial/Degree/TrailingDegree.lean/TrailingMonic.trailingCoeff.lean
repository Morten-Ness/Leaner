import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem TrailingMonic.trailingCoeff {p : R[X]} (hp : p.TrailingMonic) : Polynomial.trailingCoeff p = 1 := hp

