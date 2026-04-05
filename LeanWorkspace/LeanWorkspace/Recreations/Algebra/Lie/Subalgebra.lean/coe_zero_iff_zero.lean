import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 := (LieSubalgebra.ext_iff L' x 0).symm

