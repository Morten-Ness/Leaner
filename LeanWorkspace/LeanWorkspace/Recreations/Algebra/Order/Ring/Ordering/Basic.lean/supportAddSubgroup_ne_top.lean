import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem supportAddSubgroup_ne_top : P.supportAddSubgroup ≠ ⊤ := fun h => RingPreordering.neg_one_notMem P (by simp [h] : 1 ∈ P.supportAddSubgroup).2

