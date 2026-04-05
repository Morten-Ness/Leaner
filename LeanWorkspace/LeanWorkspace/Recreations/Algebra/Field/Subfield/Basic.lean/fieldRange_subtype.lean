import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem fieldRange_subtype (s : Subfield K) : s.subtype.fieldRange = s := SetLike.ext' <| (coe_rangeS _).trans Subtype.range_coe

