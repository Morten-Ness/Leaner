import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem isZero_iff_eq_zero [Nontrivial (LieModule.genWeightSpace M (0 : L → R))] {χ : LieModule.Weight R L M} :
    χ.IsZero ↔ χ = 0 := LieModule.Weight.ext_iff' (χ₂ := 0)

