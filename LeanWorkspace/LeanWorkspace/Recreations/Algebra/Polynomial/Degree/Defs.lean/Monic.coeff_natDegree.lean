import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem Monic.coeff_natDegree {p : R[X]} (hp : p.Monic) : p.coeff p.natDegree = 1 := hp

