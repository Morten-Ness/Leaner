import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem rootSet_neg (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    (-p).rootSet S = p.rootSet S := by
  rw [Polynomial.rootSet, Polynomial.aroots_neg, Polynomial.rootSet]

