import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem eq_rootSpace_zero_iff_isCartan [IsNoetherian R L] :
    H.toLieSubmodule = rootSpace H 0 ↔ H.IsCartanSubalgebra := by
  rw [← LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan, ← LieSubalgebra.toSubmodule_inj,
    ← LieSubmodule.toSubmodule_inj]
  aesop

