import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem coe_lieSpan_submodule_eq_iff {p : Submodule R L} :
    (LieSubalgebra.lieSpan R L (p : Set L) : Submodule R L) = p ↔ ∃ K : LieSubalgebra R L, ↑K = p := by
  rw [p.exists_lieSubalgebra_coe_eq_iff]; constructor <;> intro h
  · intro x m hm
    rw [← h, LieSubalgebra.mem_toSubmodule]
    exact LieSubalgebra.lie_mem _ (LieSubalgebra.subset_lieSpan hm)
  · rw [← LieSubalgebra.toSubmodule_mk p @h, LieSubalgebra.coe_toSubmodule, LieSubalgebra.toSubmodule_inj, LieSubalgebra.lieSpan_eq]

