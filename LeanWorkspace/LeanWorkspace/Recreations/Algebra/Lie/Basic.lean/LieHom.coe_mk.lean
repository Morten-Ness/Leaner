import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R]

variable [LieRing L₁] [LieAlgebra R L₁]

variable [LieRing L₂] [LieAlgebra R L₂]

variable [LieRing L₃] [LieAlgebra R L₃]

theorem coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) : ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f := rfl

