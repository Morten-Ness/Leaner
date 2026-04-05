import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem centralizer_toSubmonoid {R} [Ring R] (s : Set R) :
    (Subring.centralizer s).toSubmonoid = Submonoid.centralizer s := rfl

