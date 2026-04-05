import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

theorem mem_inf (x : L) : x ∈ K ⊓ K' ↔ x ∈ K ∧ x ∈ K' := by
  rw [← LieSubalgebra.mem_toSubmodule, ← LieSubalgebra.mem_toSubmodule, ← LieSubalgebra.mem_toSubmodule, LieSubalgebra.inf_toSubmodule,
    Submodule.mem_inf]

