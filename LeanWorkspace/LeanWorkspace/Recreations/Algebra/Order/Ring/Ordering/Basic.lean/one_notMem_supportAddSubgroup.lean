import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem one_notMem_supportAddSubgroup : 1 ∉ P.supportAddSubgroup := fun h => RingPreordering.neg_one_notMem P h.2

