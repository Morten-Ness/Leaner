import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem nnratCast_mem (s : S) (q : ℚ≥0) : (q : K) ∈ s := by
  simpa only [NNRat.cast_def] using div_mem (natCast_mem s q.num) (natCast_mem s q.den)

