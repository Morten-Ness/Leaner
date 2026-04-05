import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem mem_carrier {s : Subsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

