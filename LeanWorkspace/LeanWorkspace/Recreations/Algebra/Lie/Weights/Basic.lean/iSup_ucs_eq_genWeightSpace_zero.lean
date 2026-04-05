import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem iSup_ucs_eq_genWeightSpace_zero [IsNoetherian R M] :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k = LieModule.genWeightSpace M (0 : L → R) := by
  obtain ⟨k, hk⟩ := (LieSubmodule.isNilpotent_iff_exists_self_le_ucs
    <| LieModule.genWeightSpace M (0 : L → R)).mp inferInstance
  refine le_antisymm (LieModule.iSup_ucs_le_genWeightSpace_zero R L M) (le_trans hk ?_)
  exact le_iSup (fun k ↦ (⊥ : LieSubmodule R L M).ucs k) k

