import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem centralizer_toNonUnitalSubring {R} [Ring R] (s : Set R) :
    (Subring.centralizer s).toNonUnitalSubring = NonUnitalSubring.centralizer s := rfl

