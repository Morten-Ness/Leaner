import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]

variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

theorem symm_bijective : Function.Bijective (LieEquiv.symm : (L₁ ≃ₗ⁅R⁆ L₂) → L₂ ≃ₗ⁅R⁆ L₁) := Function.bijective_iff_has_inverse.mpr ⟨_, LieEquiv.symm_symm, LieEquiv.symm_symm⟩

