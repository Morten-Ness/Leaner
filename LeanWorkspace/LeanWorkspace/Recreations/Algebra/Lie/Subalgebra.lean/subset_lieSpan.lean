import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem subset_lieSpan : s ⊆ LieSubalgebra.lieSpan R L s := by
  intro m hm
  rw [SetLike.mem_coe, LieSubalgebra.mem_lieSpan]
  intro K hK
  exact hK hm

