import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem zsmul_mem {x : K} (hx : x ∈ s) (n : ℤ) : n • x ∈ s := zsmul_mem hx n

