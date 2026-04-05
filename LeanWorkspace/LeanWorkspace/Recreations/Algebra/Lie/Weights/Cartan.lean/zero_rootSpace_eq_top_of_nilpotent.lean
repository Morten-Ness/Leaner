import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem zero_rootSpace_eq_top_of_nilpotent [LieRing.IsNilpotent L] :
    rootSpace (⊤ : LieSubalgebra R L) 0 = ⊤ := zero_genWeightSpace_eq_top_of_nilpotent L

