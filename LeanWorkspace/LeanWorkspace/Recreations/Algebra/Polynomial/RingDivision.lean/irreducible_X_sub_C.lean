import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem irreducible_X_sub_C (r : R) : Irreducible (Polynomial.X - Polynomial.C r) := (Polynomial.prime_X_sub_C r).irreducible

