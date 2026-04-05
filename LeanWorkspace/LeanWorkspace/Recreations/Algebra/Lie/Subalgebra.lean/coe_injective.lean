import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem coe_injective : Function.Injective ((↑) : LieSubalgebra R L → Set L) := SetLike.coe_injective

