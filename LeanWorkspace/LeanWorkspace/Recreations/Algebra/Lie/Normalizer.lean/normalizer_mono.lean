import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

theorem normalizer_mono (h : N₁ ≤ N₂) : LieSubmodule.normalizer N₁ ≤ LieSubmodule.normalizer N₂ := by
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm ⊢
  exact fun x ↦ h (hm x)

