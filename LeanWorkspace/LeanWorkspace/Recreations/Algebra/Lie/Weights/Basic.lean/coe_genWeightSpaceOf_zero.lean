import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem coe_genWeightSpaceOf_zero (x : L) :
    ↑(LieModule.genWeightSpaceOf M (0 : R) x) = ⨆ k, LinearMap.ker (toEnd R L M x ^ k) := by
  simp [LieModule.genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq]

