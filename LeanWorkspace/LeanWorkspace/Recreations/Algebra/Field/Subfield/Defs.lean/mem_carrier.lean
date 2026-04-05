import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_carrier {s : Subfield K} {x : K} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

