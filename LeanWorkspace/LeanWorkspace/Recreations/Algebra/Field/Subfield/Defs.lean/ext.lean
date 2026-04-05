import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem ext {S T : Subfield K} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

