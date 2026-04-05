import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem mem_carrier {x : L} : x ∈ L'.carrier ↔ x ∈ (L' : Set L) := Iff.rfl

