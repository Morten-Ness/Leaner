import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Module R M] [Module R N] [Module R P]

variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

theorem coe_mk (f : M →ₗ⁅R,L⁆ N) (invFun h₁ h₂) :
    ((⟨f, invFun, h₁, h₂⟩ : M ≃ₗ⁅R,L⁆ N) : M → N) = f := rfl

