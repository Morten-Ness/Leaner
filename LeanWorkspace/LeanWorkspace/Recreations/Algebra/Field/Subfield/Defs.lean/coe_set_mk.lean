import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem coe_set_mk (S : Subring K) (h) : ((⟨S, h⟩ : Subfield K) : Set K) = S := rfl

