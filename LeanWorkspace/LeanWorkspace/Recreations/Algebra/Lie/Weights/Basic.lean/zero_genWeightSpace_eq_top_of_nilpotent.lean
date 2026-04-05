import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem zero_genWeightSpace_eq_top_of_nilpotent [IsNilpotent L M] :
    LieModule.genWeightSpace M (0 : (⊤ : LieSubalgebra R L) → R) = ⊤ := by
  simp_all

