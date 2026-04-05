import Mathlib

variable (R : Type*) [CommRing R]

theorem mem_mk {toSubsemiring : Subsemiring R} (RingPreordering.mem_of_isSquare RingPreordering.neg_one_notMem) {x : R} :
    x ∈ RingPreordering.mk toSubsemiring RingPreordering.mem_of_isSquare RingPreordering.neg_one_notMem ↔ x ∈ toSubsemiring := .rfl

