import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocRing R] [NonAssocRing S] (f : R ≃+* S)

theorem map_neg_one : f (-1) = -1 := RingEquiv.map_one f ▸ RingEquiv.map_neg f 1

