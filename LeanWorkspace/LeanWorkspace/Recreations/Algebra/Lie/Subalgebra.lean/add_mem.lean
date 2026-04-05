import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem add_mem {x y : L} : x ∈ L' → y ∈ L' → (x + y : L) ∈ L' := add_mem

