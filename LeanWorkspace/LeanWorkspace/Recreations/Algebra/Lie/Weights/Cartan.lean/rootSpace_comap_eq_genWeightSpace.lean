import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem rootSpace_comap_eq_genWeightSpace (χ : H → R) :
    (rootSpace H χ).comap H.incl' = genWeightSpace H χ := comap_genWeightSpace_eq_of_injective Subtype.coe_injective

