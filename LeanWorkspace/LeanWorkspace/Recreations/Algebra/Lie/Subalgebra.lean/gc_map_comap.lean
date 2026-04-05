import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

theorem gc_map_comap : GaloisConnection (LieSubalgebra.map f) (LieSubalgebra.comap f) := fun _ _ ↦ LieSubalgebra.map_le_iff_le_comap

