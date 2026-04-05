import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N]

variable (f : M →ₗ⁅R,L⁆ N)

theorem le_ker_iff_map (M' : LieSubmodule R L M) : M' ≤ f.ker ↔ LieSubmodule.map f M' = ⊥ := by
  rw [LieModuleHom.ker, eq_bot_iff, LieSubmodule.map_le_iff_le_comap]

