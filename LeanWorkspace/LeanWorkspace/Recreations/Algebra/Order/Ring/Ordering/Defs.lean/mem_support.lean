import Mathlib

variable (R : Type*) [CommRing R]

variable {P : RingPreordering R}

variable [P.HasIdealSupport]

theorem mem_support {x} : x ∈ P.support ↔ x ∈ P ∧ -x ∈ P := .rfl

