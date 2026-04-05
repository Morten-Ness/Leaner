import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem isNilpotent_toEnd_genWeightSpace_zero [IsNoetherian R M] (x : L) :
    _root_.IsNilpotent <| toEnd R L (LieModule.genWeightSpace M (0 : L → R)) x := by
  simpa using LieModule.isNilpotent_toEnd_sub_algebraMap M (0 : L → R) x

