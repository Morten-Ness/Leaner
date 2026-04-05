import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Polynomial.Monic p) : Irreducible p := (hm.prime_of_degree_eq_one hp1).irreducible

