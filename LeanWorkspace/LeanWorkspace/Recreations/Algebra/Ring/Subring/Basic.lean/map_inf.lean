import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem map_inf (s t : Subring R) (f : R →+* S) (hf : Function.Injective f) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter hf)

