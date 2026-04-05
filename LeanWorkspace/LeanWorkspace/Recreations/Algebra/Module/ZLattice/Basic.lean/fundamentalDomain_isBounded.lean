import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

theorem fundamentalDomain_isBounded [Finite ι] [HasSolidNorm K] :
    IsBounded (ZSpan.fundamentalDomain b) := by
  cases nonempty_fintype ι
  refine isBounded_iff_forall_norm_le.2 ⟨∑ j, ‖b j‖, fun x hx ↦ ?_⟩
  rw [← ZSpan.fract_eq_self.mpr hx]
  apply ZSpan.norm_fract_le

