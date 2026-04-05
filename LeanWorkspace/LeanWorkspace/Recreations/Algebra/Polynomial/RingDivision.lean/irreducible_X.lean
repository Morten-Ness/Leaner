import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem irreducible_X : Irreducible (Polynomial.X : R[X]) := Prime.irreducible Polynomial.prime_X

