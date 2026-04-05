import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem mem_toSubsemiring {S : StarSubsemiring R} {x} : x ∈ S.toSubsemiring ↔ x ∈ S := Iff.rfl

