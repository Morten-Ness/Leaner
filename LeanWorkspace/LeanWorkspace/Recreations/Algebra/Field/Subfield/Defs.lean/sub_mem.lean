import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem sub_mem {x y : K} : x ∈ s → y ∈ s → x - y ∈ s := sub_mem

