import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem range_subtype (s : Subring R) : s.subtype.range = s := SetLike.coe_injective <| (coe_rangeS _).trans Subtype.range_coe

