import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem mem_toSubsemiring {s : Subring R} {x : R} : x ∈ s.toSubsemiring ↔ x ∈ s := Iff.rfl

