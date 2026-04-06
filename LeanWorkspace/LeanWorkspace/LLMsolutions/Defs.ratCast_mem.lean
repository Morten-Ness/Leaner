import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem ratCast_mem (s : S) (q : ℚ) : (q : K) ∈ s := by
  simpa using SubfieldClass.ratCast_mem (s := s) q
