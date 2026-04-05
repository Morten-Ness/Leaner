import Mathlib

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

variable [Module.Finite R L]

variable [LieAlgebra.IsKilling R L]

theorem killingForm_restrict_range_ad_nondegenerate :
    ((killingForm R 𝔻).restrict 𝕀).Nondegenerate := by
  convert LieAlgebra.IsKilling.killingForm_nondegenerate R 𝕀
  exact LieDerivation.IsKilling.killingForm_restrict_range_ad R L

