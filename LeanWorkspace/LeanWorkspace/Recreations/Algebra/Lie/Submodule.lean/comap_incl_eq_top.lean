import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

theorem comap_incl_eq_top : N₂.comap N.incl = ⊤ ↔ N ≤ N₂ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.toSubmodule_comap, LieSubmodule.incl_coe,
    LieSubmodule.top_toSubmodule, Submodule.comap_subtype_eq_top, LieSubmodule.toSubmodule_le_toSubmodule]

