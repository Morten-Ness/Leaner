import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

theorem map_le_iff_le_comap {K : LieSubalgebra R L} {K' : LieSubalgebra R L₂} :
    LieSubalgebra.map f K ≤ K' ↔ K ≤ LieSubalgebra.comap f K' := Set.image_subset_iff

