import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem coe_set_eq (L₁' L₂' : LieSubalgebra R L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' := SetLike.coe_set_eq

