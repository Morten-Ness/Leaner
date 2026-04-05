import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

theorem sInf_toSubmodule (S : Set (LieSubalgebra R L)) :
    (↑(sInf S) : Submodule R L) = sInf {(s : Submodule R L) | s ∈ S} := rfl

