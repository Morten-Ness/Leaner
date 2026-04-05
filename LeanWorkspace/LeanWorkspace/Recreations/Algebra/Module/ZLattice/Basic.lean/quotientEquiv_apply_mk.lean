import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

theorem quotientEquiv_apply_mk [Fintype ι] (x : E) :
    ZSpan.quotientEquiv b (Submodule.Quotient.mk x) = ZSpan.fractRestrict b x := rfl

