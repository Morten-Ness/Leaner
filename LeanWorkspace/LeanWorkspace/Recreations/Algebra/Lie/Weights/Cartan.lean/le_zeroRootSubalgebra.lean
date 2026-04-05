import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem le_zeroRootSubalgebra : H ≤ LieAlgebra.zeroRootSubalgebra R L H := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, ← H.coe_toLieSubmodule,
    LieAlgebra.coe_zeroRootSubalgebra, LieSubmodule.toSubmodule_le_toSubmodule]
  exact LieAlgebra.toLieSubmodule_le_rootSpace_zero R L H

