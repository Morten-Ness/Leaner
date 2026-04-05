import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem coe_zero [Nontrivial (LieModule.genWeightSpace M (0 : L → R))] : ((0 : LieModule.Weight R L M) : L → R) = 0 := rfl

