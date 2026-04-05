import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem lieSpan_le {K} : LieSubalgebra.lieSpan R L s ≤ K ↔ s ⊆ K := by
  constructor
  · exact Set.Subset.trans LieSubalgebra.subset_lieSpan
  · intro hs m hm
    rw [LieSubalgebra.mem_lieSpan] at hm
    exact hm _ hs

