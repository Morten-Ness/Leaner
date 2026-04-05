import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : (S.copy s hs : Set K) = s := rfl

