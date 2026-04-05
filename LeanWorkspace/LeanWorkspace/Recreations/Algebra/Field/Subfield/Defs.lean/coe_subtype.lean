import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem coe_subtype : ⇑(s.subtype) = ((↑) : s → K) := rfl

