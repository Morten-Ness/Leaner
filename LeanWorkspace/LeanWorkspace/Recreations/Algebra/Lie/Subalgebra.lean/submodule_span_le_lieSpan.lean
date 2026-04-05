import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem submodule_span_le_lieSpan : Submodule.span R s ≤ LieSubalgebra.lieSpan R L s := by
  rw [Submodule.span_le, LieSubalgebra.coe_toSubmodule]
  apply LieSubalgebra.subset_lieSpan

