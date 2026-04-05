import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem centralizer_toSubsemiring {R} [Ring R] (s : Set R) :
    (Subring.centralizer s).toSubsemiring = Subsemiring.centralizer s := rfl

