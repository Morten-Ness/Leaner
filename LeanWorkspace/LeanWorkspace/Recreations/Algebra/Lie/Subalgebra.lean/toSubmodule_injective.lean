import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

theorem toSubmodule_injective : Function.Injective ((↑) : LieSubalgebra R L → Submodule R L) := fun L₁' L₂' h ↦ by
  rw [SetLike.ext'_iff] at h
  rw [← LieSubalgebra.coe_set_eq]
  exact h

