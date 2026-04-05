import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem mem_carrier {s : StarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

