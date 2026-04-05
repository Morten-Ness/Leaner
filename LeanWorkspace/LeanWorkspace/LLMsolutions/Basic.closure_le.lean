import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_le {s : Set K} {t : Subfield K} : Subfield.closure s ≤ t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    exact h (Subfield.subset_closure hx)
  · intro h
    exact Subfield.closure_le.2 h
