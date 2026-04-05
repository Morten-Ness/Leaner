import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem exists_ne_zero (χ : LieModule.Weight R L M) :
    ∃ x ∈ LieModule.genWeightSpace M χ, x ≠ 0 := by
  simpa [LieSubmodule.eq_bot_iff] using χ.genWeightSpace_ne_bot

