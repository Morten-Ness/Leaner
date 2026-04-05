import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem lieSpan_eq : LieSubalgebra.lieSpan R L (K : Set L) = K := le_antisymm (LieSubalgebra.lieSpan_le.mpr rfl.subset) LieSubalgebra.subset_lieSpan

