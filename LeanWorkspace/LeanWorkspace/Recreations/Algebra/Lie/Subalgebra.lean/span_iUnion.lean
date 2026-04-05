import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem span_iUnion {ι} (s : ι → Set L) : LieSubalgebra.lieSpan R L (⋃ i, s i) = ⨆ i, LieSubalgebra.lieSpan R L (s i) := (LieSubalgebra.gi R L).gc.l_iSup

