import Mathlib

variable (R : Type*) [CommRing R]

theorem coe_toSubsemiring (P : RingPreordering R) : (P.toSubsemiring : Set R) = P := rfl

