import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem iSup_ucs_le_genWeightSpace_zero :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k ≤ LieModule.genWeightSpace M (0 : L → R) := by
  simpa using
    LieSubmodule.ucs_le_of_normalizer_eq_self (LieModule.genWeightSpace_zero_normalizer_eq_self R L M)

