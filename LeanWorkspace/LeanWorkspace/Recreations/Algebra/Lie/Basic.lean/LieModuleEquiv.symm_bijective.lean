import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Module R M] [Module R N] [Module R P]

variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

theorem symm_bijective :
    Function.Bijective (LieModuleEquiv.symm : (M ≃ₗ⁅R,L⁆ N) → N ≃ₗ⁅R,L⁆ M) := Function.bijective_iff_has_inverse.mpr ⟨_, LieModuleEquiv.symm_symm, LieModuleEquiv.symm_symm⟩

