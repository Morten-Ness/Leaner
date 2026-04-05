import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem zpow_mem {x : K} (hx : x ∈ s) (n : ℤ) : x ^ n ∈ s := zpow_mem hx n

