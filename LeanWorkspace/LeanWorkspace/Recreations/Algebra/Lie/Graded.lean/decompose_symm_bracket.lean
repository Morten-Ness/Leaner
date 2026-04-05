import Mathlib

open scoped DirectSum

variable {ι σ R L : Type*}

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

theorem decompose_symm_bracket (x y : ⨁ i, ℒ i) :
    (decompose ℒ).symm ⁅x, y⁆  = ⁅(decompose ℒ).symm x, (decompose ℒ).symm y⁆ := by
  simp only [← decomposeLinearEquiv_symm_apply]
  simp

