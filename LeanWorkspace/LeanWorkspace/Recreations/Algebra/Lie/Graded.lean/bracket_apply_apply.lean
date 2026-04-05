import Mathlib

open scoped DirectSum

variable {ι σ R L : Type*}

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

theorem bracket_apply_apply (x y : ⨁ i, ℒ i) :
    ⁅x, y⁆ =
      decomposeLinearEquiv ℒ ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆ := rfl

attribute [local simp] bracket_apply_apply

