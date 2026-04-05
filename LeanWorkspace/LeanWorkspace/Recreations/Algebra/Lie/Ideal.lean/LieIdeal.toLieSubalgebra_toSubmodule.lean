import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable [LieAlgebra R L] [LieModule R L M]

theorem LieIdeal.toLieSubalgebra_toSubmodule (I : LieIdeal R L) :
    ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule.toSubmodule I := rfl

