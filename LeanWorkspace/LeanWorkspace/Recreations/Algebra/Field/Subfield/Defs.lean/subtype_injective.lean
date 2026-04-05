import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

theorem subtype_injective (s : Subfield K) :
    Function.Injective s.subtype := Subtype.coe_injective

