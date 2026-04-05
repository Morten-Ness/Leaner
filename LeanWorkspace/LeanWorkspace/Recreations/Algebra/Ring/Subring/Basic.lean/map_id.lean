import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem map_id : s.map (RingHom.id R) = s := SetLike.coe_injective <| Set.image_id _

