import Mathlib

variable (R : Type*) [CommRing R]

theorem mem_toSubsemiring {P : RingPreordering R} {x : R} : x ∈ P.toSubsemiring ↔ x ∈ P := .rfl

