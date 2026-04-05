import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem mem_toAddSubgroup {s : Subfield K} {x : K} : x ∈ s.toAddSubgroup ↔ x ∈ s := Iff.rfl

