import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

theorem comap_normalizer (f : M' →ₗ⁅R,L⁆ M) : N.normalizer.comap f = (N.comap f).normalizer := by
  ext; simp

