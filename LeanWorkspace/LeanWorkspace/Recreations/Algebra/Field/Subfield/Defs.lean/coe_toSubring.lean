import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_toSubring (s : Subfield K) : (s.toSubring : Set K) = s := rfl

