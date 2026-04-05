import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem intCast_mem (n : ℤ) : (n : K) ∈ s := intCast_mem s n

