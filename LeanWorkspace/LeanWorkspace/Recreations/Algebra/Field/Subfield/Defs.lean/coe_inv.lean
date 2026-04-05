import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem coe_inv (x : s) : (↑x⁻¹ : K) = (↑x)⁻¹ := rfl

