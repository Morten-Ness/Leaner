import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem is_cartan_of_zeroRootSubalgebra_eq (h : LieAlgebra.zeroRootSubalgebra R L H = H) :
    H.IsCartanSubalgebra := { nilpotent := inferInstance
    self_normalizing := by rw [← h]; exact LieAlgebra.zeroRootSubalgebra_normalizer_eq_self R L H }

