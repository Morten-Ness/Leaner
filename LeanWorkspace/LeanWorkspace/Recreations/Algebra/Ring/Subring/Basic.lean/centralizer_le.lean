import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem centralizer_le {R} [Ring R] (s t : Set R) (h : s ⊆ t) : Subring.centralizer t ≤ Subring.centralizer s := Set.centralizer_subset h

