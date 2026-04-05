import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

theorem quotientEquiv.symm_apply [Fintype ι] (x : ZSpan.fundamentalDomain b) :
    (ZSpan.quotientEquiv b).symm x = Submodule.Quotient.mk ↑x := by
  rw [Equiv.symm_apply_eq, ZSpan.quotientEquiv_apply_mk b ↑x, Subtype.ext_iff, ZSpan.fractRestrict_apply]
  exact (ZSpan.fract_eq_self.mpr x.prop).symm

