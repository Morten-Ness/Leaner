import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem coe_comap (s : Subfield L) : (s.comap f : Set K) = f ⁻¹' s := rfl

