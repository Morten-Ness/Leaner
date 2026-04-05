import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (g : L →+* M) (f : K →+* L)

theorem fieldRange_eq_top_iff {f : K →+* L} :
    f.fieldRange = ⊤ ↔ Function.Surjective f := SetLike.ext'_iff.trans Set.range_eq_univ

