import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

theorem coe_sInf (S : Set (LieSubalgebra R L)) : (↑(sInf S) : Set L) = ⋂ s ∈ S, (s : Set L) := by
  rw [← LieSubalgebra.coe_toSubmodule, LieSubalgebra.sInf_toSubmodule, Submodule.coe_sInf]
  ext x
  simp

