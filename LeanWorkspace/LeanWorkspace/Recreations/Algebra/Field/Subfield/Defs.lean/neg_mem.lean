import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem neg_mem {x : K} : x ∈ s → -x ∈ s := neg_mem

