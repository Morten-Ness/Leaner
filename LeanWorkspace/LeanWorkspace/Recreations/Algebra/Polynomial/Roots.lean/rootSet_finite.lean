import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem rootSet_finite (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    (p.rootSet S).Finite := Set.toFinite _

