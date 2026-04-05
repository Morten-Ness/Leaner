import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_toSubring (s : Subfield K) (x : K) : x ∈ s.toSubring ↔ x ∈ s := Iff.rfl

