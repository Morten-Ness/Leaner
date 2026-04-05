import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem lieSpan_mono {t : Set L} (h : s ⊆ t) : LieSubalgebra.lieSpan R L s ≤ LieSubalgebra.lieSpan R L t := by
  rw [LieSubalgebra.lieSpan_le]
  exact Set.Subset.trans h LieSubalgebra.subset_lieSpan

