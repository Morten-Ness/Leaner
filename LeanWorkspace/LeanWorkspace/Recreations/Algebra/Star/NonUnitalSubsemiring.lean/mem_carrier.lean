import Mathlib

variable {A : Type v} {B : Type w} {C : Type w'}

variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]

theorem mem_carrier {s : NonUnitalStarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

