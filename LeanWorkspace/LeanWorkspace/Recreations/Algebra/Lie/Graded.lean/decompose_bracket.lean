import Mathlib

variable {ι σ R L : Type*}

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

theorem decompose_bracket (x y : L) : decompose ℒ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℒ y⁆ := by
  simp only [← decomposeLinearEquiv_apply]
  simp

