import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N]

variable (f : M →ₗ⁅R,L⁆ N)

theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff, LieModuleHom.coe_range, LieSubmodule.top_coe, Set.range_eq_univ]

