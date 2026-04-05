import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_le {s : Set K} {t : Subfield K} : Subfield.closure s ≤ t ↔ s ⊆ t := ⟨Set.Subset.trans Subfield.subset_closure, fun h _ hx => Subfield.mem_closure.mp hx t h⟩

