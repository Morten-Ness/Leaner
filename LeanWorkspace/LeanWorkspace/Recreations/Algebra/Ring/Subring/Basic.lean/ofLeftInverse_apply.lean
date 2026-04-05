import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s t : Subring R}

theorem ofLeftInverse_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(RingEquiv.ofLeftInverse h x) = f x := rfl

