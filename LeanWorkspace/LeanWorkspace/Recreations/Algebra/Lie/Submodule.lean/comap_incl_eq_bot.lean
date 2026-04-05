import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

theorem comap_incl_eq_bot : N₂.comap N.incl = ⊥ ↔ N ⊓ N₂ = ⊥ := by
  simp only [← LieSubmodule.toSubmodule_inj, LieSubmodule.toSubmodule_comap, LieSubmodule.incl_coe, LieSubmodule.bot_toSubmodule,
    LieSubmodule.inf_toSubmodule]
  rw [← Submodule.disjoint_iff_comap_eq_bot, disjoint_iff]

