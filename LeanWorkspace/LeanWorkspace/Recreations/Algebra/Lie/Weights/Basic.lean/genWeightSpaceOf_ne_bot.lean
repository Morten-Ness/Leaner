import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem genWeightSpaceOf_ne_bot (χ : LieModule.Weight R L M) (x : L) :
    LieModule.genWeightSpaceOf M (χ x) x ≠ ⊥ := by
  have : ⨅ x, LieModule.genWeightSpaceOf M (χ x) x ≠ ⊥ := χ.genWeightSpace_ne_bot
  contrapose! this
  rw [eq_bot_iff]
  exact le_of_le_of_eq (iInf_le _ _) this

