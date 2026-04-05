import Mathlib

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

variable [Module.Finite R L]

variable [LieAlgebra.IsKilling R L]

set_option backward.isDefEq.respectTransparency false in
theorem range_ad_eq_top : 𝕀 = ⊤ := by
  rw [← LieSubalgebra.toSubmodule_inj]
  apply LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl (LieDerivation.IsKilling.killingForm_restrict_range_ad_nondegenerate R L)
  refine (Submodule.eq_bot_iff _).mpr fun D hD ↦ ext fun x ↦ ?_
  simpa using LieDerivation.IsKilling.ad_mem_ker_killingForm_ad_range_of_mem_orthogonal hD x

