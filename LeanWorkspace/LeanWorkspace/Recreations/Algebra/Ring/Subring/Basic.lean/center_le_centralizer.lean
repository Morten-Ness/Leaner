import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem center_le_centralizer {R} [Ring R] (s) : Subring.center R ≤ Subring.centralizer s := s.center_subset_centralizer

