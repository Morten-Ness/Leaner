import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem zeroRootSubalgebra_eq_iff_is_cartan [IsNoetherian R L] :
    LieAlgebra.zeroRootSubalgebra R L H = H ↔ H.IsCartanSubalgebra := ⟨LieAlgebra.is_cartan_of_zeroRootSubalgebra_eq R L H, by intros; simp⟩

