import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem mem_mk_iff' (p : Submodule R L) (h) {x : L} :
    x ∈ (⟨p, h⟩ : LieSubalgebra R L) ↔ x ∈ p := Iff.rfl

