import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem coe_rangeRestrictField (f : K →+* L) (x : K) : (f.rangeRestrictField x : L) = f x := rfl

