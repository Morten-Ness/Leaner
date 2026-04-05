import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_mono ⦃s t : Set K⦄ (h : s ⊆ t) : Subfield.closure s ≤ Subfield.closure t := Subfield.closure_le.2 <| Set.Subset.trans h Subfield.subset_closure

