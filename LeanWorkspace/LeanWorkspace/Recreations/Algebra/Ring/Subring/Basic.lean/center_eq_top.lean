import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem center_eq_top (R) [CommRing R] : Subring.center R = ⊤ := SetLike.coe_injective (Set.center_eq_univ R)

