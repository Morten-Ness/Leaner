import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem smul_mem (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' := SMulMemClass.smul_mem _ h

