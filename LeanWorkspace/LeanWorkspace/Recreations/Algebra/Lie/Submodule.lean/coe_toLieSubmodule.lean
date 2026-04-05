import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable [LieAlgebra R L]

variable (K : LieSubalgebra R L)

theorem coe_toLieSubmodule : (K.toLieSubmodule : Submodule R L) = K := rfl

