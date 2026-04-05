import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem toSubring_subtype_eq_subtype (S : Subfield K) :
    S.toSubring.subtype = S.subtype := rfl

