import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem pow_mem {x : K} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s := pow_mem hx n

