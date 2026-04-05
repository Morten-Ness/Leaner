import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem ext_iff (x y : L') : x = y ↔ (x : L) = y := Subtype.ext_iff

