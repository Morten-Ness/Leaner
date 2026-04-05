import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem mem_coe {x : L} : x ∈ (L' : Set L) ↔ x ∈ L' := Iff.rfl

