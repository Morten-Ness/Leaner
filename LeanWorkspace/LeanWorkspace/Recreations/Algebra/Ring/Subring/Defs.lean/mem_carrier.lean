import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem mem_carrier {s : Subring R} {x : R} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

