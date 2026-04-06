import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem mem_iInf {ι : Sort*} {S : ι → Subfield K} {x : K} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp [Subfield.mem_iInf]
