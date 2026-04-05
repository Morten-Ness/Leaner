import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_iInf {ι : Sort*} {S : ι → Subfield K} : (↑(⨅ i, S i) : Set K) = ⋂ i, S i := by
  ext x
  simp [Subfield.mem_iInf]
