import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem weightSpace_le_genWeightSpace (χ : L → R) :
    LieModule.weightSpace M χ ≤ LieModule.genWeightSpace M χ := by
  apply le_iInf
  intro x
  rw [← (LieSubmodule.toSubmodule_orderEmbedding R L M).le_iff_le]
  apply (iInf_le _ x).trans
  exact ((toEnd R L M x).genEigenspace (χ x)).monotone le_top

