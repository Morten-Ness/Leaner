import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem coe_zeroRootSubalgebra : (LieAlgebra.zeroRootSubalgebra R L H : Submodule R L) = rootSpace H 0 := rfl

