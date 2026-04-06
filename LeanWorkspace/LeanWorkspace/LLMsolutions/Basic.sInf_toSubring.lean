import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem sInf_toSubring (s : Set (Subfield K)) :
    (sInf s).toSubring = ⨅ t ∈ s, Subfield.toSubring t := by
  ext x
  simp [Subring.mem_iInf, Subfield.mem_sInf]
