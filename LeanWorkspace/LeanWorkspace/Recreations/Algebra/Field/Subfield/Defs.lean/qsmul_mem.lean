import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem qsmul_mem (s : S) (q : ℚ) (hx : x ∈ s) : q • x ∈ s := by
  simpa only [Rat.smul_def] using mul_mem (SubfieldClass.ratCast_mem _ _) hx

