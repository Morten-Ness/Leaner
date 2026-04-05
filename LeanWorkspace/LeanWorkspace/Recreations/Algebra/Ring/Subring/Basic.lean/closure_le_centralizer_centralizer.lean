import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem closure_le_centralizer_centralizer {R} [Ring R] (s : Set R) :
    Subring.closure s ≤ Subring.centralizer (Subring.centralizer s) := Subring.closure_le.mpr Set.subset_centralizer_centralizer

