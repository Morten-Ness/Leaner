import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N]

variable (f : M →ₗ⁅R,L⁆ N)

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.toSubmodule_inj, LieModuleHom.ker_toSubmodule, LieSubmodule.bot_toSubmodule,
    LinearMap.ker_eq_bot, coe_toLinearMap]

