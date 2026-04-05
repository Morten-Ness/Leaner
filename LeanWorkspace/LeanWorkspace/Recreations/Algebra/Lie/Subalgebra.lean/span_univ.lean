import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem span_univ : LieSubalgebra.lieSpan R L (Set.univ : Set L) = ⊤ := eq_top_iff.2 <| SetLike.le_def.2 <| LieSubalgebra.subset_lieSpan

