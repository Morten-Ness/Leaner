import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem centralizer_eq_top_iff_subset {R} [Ring R] {s : Set R} : Subring.centralizer s = ⊤ ↔ s ⊆ Subring.center R := SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

