import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem genWeightSpace_le_genWeightSpaceOf (x : L) (χ : L → R) :
    LieModule.genWeightSpace M χ ≤ LieModule.genWeightSpaceOf M (χ x) x := iInf_le _ x

