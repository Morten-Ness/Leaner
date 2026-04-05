import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem centralizer_univ {R} [Ring R] : Subring.centralizer Set.univ = Subring.center R := SetLike.ext' (Set.centralizer_univ R)

