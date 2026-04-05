import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem maxTrivSubmodule_eq_bot_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
    LieModule.maxTrivSubmodule R L (LieDerivation R L L) = ⊥ := by
  refine (LieSubmodule.eq_bot_iff _).mpr fun D hD ↦ ext fun x ↦ ?_
  have : LieDerivation.ad R L (D x) = 0 := by
    rw [LieModule.mem_maxTrivSubmodule] at hD
    simp [LieDerivation.ad_apply_lieDerivation, hD]
  rw [← LieHom.mem_ker, LieDerivation.ad_ker_eq_center, h, LieSubmodule.mem_bot] at this
  simp [this]

