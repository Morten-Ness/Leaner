import Mathlib

variable (R : Type*) [CommRing R]

variable {P : RingPreordering R}

variable [P.HasIdealSupport]

theorem coe_support : P.support = (P : Set R) ∩ -(P : Set R) := rfl

