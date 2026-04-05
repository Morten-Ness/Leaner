import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem map_comap_eq (f : R →+* S) (t : Subring S) : (t.comap f).map f = t ⊓ f.range := SetLike.coe_injective Set.image_preimage_eq_inter_range

