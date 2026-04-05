import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem coe_toSubmodule : ((L' : Submodule R L) : Set L) = L' := rfl

