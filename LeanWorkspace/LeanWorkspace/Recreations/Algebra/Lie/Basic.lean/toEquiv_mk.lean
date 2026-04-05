import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Module R M] [Module R N] [Module R P]

variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

theorem toEquiv_mk (f : M →ₗ⁅R,L⁆ N) (g : N → M) (h₁ h₂) :
    LieModuleEquiv.toEquiv (LieModuleEquiv.mk f g h₁ h₂ : M ≃ₗ⁅R,L⁆ N) = Equiv.mk f g h₁ h₂ := rfl

