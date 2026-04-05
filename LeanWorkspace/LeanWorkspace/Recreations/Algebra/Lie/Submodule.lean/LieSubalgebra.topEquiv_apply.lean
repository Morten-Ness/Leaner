import Mathlib

variable (R : Type u) (L : Type v)

variable [CommRing R] [LieRing L]

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [LieAlgebra R L] [LieModule R L M]

theorem LieSubalgebra.topEquiv_apply (x : (⊤ : LieSubalgebra R L)) : LieSubalgebra.topEquiv x = x := rfl

