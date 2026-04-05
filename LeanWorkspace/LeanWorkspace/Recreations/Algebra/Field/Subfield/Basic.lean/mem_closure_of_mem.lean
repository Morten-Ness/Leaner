import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_closure_of_mem {s : Set K} {x : K} (hx : x ∈ s) : x ∈ Subfield.closure s := Subfield.subset_closure hx

