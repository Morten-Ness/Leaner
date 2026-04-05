import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Set K}

theorem closure_preimage_le (f : K →+* L) (s : Set L) : Subfield.closure (f ⁻¹' s) ≤ (Subfield.closure s).comap f := by
  refine Subfield.closure_le.2 ?_
  intro x hx
  change f x ∈ Subfield.closure s
  exact Subfield.subset_closure hx
