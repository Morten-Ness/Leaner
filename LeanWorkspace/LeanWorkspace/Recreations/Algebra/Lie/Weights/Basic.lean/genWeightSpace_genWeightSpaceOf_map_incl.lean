import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem genWeightSpace_genWeightSpaceOf_map_incl (x : L) (χ : L → R) :
    (LieModule.genWeightSpace (LieModule.genWeightSpaceOf M (χ x) x) χ).map (LieModule.genWeightSpaceOf M (χ x) x).incl =
    LieModule.genWeightSpace M χ := by
  simpa [LieModule.map_genWeightSpace_eq_of_injective (LieModule.genWeightSpaceOf M (χ x) x).injective_incl]
    using LieModule.genWeightSpace_le_genWeightSpaceOf M x χ

