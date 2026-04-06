import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem subring_closure_le (s : Set K) : Subring.closure s ≤ (Subfield.closure s).toSubring := by
  refine Subring.closure_le.2 ?_
  intro x hx
  exact Subfield.subset_closure hx
