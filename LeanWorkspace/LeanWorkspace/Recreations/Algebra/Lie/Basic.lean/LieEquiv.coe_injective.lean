import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]

variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

theorem coe_injective : @Function.Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ → L₂) (↑) := LinearEquiv.coe_injective.comp LieEquiv.toLinearEquiv_injective

