import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem ratCast_mem (s : S) (q : ℚ) : (q : K) ∈ s := by
  simpa only [Rat.cast_def] using div_mem (intCast_mem s q.num) (natCast_mem s q.den)

