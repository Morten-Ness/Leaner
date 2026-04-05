import Mathlib

open scoped Pointwise

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

theorem smul {c : K} (hc : c ≠ 0) :
    c • span ℤ (Set.range b) = span ℤ (Set.range (b.isUnitSMul (fun _ ↦ hc.isUnit))) := by
  rw [smul_span, Set.smul_set_range]
  congr!
  rw [Module.Basis.isUnitSMul_apply]

