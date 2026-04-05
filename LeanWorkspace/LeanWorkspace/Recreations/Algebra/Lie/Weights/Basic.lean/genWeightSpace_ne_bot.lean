import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem genWeightSpace_ne_bot (χ : LieModule.Weight R L M) : LieModule.genWeightSpace M χ ≠ ⊥ := χ.genWeightSpace_ne_bot'

