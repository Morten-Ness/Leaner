import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

variable {L : Type v} [Semiring L]

theorem eqOn_field_closure {f g : K →+* L} {s : Set K} (h : Set.EqOn f g s) :
    Set.EqOn f g (Subfield.closure s) := show Subfield.closure s ≤ f.eqLocusField g from Subfield.closure_le.2 h

