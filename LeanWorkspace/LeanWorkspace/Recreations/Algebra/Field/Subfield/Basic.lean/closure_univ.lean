import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_univ : Subfield.closure (Set.univ : Set K) = ⊤ := @Subfield.coe_top K _ ▸ Subfield.closure_eq ⊤

