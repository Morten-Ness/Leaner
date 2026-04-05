import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem coe_centralizer {R} [Ring R] (s : Set R) : (Subring.centralizer s : Set R) = s.centralizer := rfl

