import Mathlib

variable (R : Type*) [CommRing R]

variable {P : RingPreordering R}

theorem mem_supportAddSubgroup {x} : x ∈ P.supportAddSubgroup ↔ x ∈ P ∧ -x ∈ P := .rfl

