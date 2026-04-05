import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem ext (L₁' L₂' : LieSubalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' := SetLike.ext h

