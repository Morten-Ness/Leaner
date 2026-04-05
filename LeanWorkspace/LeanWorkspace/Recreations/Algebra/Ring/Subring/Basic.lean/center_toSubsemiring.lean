import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem center_toSubsemiring : (Subring.center R).toSubsemiring = Subsemiring.center R := rfl

