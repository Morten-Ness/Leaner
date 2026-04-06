import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem qsmul_mem (s : S) (q : ℚ) (hx : x ∈ s) : q • x ∈ s := by
  simpa using h.qsmul_mem s q hx
