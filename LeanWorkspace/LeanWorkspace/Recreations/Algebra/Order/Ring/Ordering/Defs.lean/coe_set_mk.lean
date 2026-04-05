import Mathlib

variable (R : Type*) [CommRing R]

theorem coe_set_mk (toSubsemiring : Subsemiring R) (RingPreordering.mem_of_isSquare RingPreordering.neg_one_notMem) :
    (RingPreordering.mk toSubsemiring RingPreordering.mem_of_isSquare RingPreordering.neg_one_notMem : Set R) = toSubsemiring := rfl

