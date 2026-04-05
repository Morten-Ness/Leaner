import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem mem_toSubmodule {x : L} : x ∈ (L' : Submodule R L) ↔ x ∈ L' := Iff.rfl

