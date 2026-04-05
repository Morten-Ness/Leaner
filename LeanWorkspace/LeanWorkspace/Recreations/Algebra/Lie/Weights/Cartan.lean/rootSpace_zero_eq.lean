import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem rootSpace_zero_eq (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L] :
    rootSpace H 0 = H.toLieSubmodule := by
  rw [← LieSubmodule.toSubmodule_inj, ← LieAlgebra.coe_zeroRootSubalgebra,
    LieAlgebra.zeroRootSubalgebra_eq_of_is_cartan R L H, LieSubalgebra.coe_toLieSubmodule]

