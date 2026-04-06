FAIL
import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S} {x : K}

theorem nnqsmul_mem (s : S) (q : ℚ≥0) (hx : x ∈ s) : q • x ∈ s := by
  obtain ⟨q, rfl⟩ := Rat.nnratCast_surjective q
  simpa [NNRat.smul_def] using h.mul_mem (h.ratCast_mem s q) hx
