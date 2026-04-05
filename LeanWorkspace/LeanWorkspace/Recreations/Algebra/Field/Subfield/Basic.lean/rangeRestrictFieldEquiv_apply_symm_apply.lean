import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

theorem rangeRestrictFieldEquiv_apply_symm_apply (f : K →+* L) (x : f.fieldRange) :
    f (f.rangeRestrictFieldEquiv.symm x) = x := by
  rw [← rangeRestrictFieldEquiv_apply_coe, RingEquiv.apply_symm_apply]

