import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_closure {x : K} {s : Set K} : x ∈ Subfield.closure s ↔ ∀ S : Subfield K, s ⊆ S → x ∈ S := Subfield.mem_sInf

