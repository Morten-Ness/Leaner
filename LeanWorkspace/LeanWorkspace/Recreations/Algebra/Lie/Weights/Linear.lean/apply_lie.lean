import Mathlib

variable (k R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] [LinearWeights R L M] (χ : Weight R L M)

theorem apply_lie (x y : L) :
    χ ⁅x, y⁆ = 0 := LinearWeights.map_lie χ χ.genWeightSpace_ne_bot x y

