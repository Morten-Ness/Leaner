import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem posFittingComp_le_iInf_lowerCentralSeries :
    LieModule.posFittingComp R L M ≤ ⨅ k, lowerCentralSeries R L M k := by
  simp [LieModule.posFittingComp]

