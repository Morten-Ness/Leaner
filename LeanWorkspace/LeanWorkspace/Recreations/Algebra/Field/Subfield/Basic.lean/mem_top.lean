import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem mem_top (x : K) : x ∈ (⊤ : Subfield K) := Set.mem_univ x

