import Mathlib

variable (R : Type*) [CommRing R]

variable {P : RingPreordering R}

theorem coe_supportAddSubgroup : P.supportAddSubgroup = (P ∩ -P : Set R) := rfl

