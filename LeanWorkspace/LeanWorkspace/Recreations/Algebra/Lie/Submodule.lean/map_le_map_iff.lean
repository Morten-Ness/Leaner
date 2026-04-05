import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

theorem map_le_map_iff (hf : Function.Injective f) :
    N.map f ≤ N₂.map f ↔ N ≤ N₂ := Set.image_subset_image_iff hf

