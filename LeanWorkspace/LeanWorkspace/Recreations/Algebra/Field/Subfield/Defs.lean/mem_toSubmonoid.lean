import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem mem_toSubmonoid {s : Subfield K} {x : K} : x ∈ s.toSubmonoid ↔ x ∈ s := Iff.rfl

