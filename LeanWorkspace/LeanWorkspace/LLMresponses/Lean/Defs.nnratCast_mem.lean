FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem nnratCast_mem (s : S) (q : ℚ≥0) : (q : K) ∈ s := by
  rw [NNRat.cast_def]
  exact div_mem (show (q.num : K) ∈ s from SubfieldClass.natCast_mem h s q.num)
    (show (q.den : K) ∈ s from SubfieldClass.natCast_mem h s q.den)
