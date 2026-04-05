import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem sub_mem {x y : L} : x ∈ L' → y ∈ L' → (x - y : L) ∈ L' := sub_mem

