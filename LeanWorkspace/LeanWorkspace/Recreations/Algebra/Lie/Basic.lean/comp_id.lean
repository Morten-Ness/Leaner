import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R]

variable [LieRing L₁] [LieAlgebra R L₁]

variable [LieRing L₂] [LieAlgebra R L₂]

variable [LieRing L₃] [LieAlgebra R L₃]

theorem comp_id (f : L₁ →ₗ⁅R⁆ L₂) : f.comp (LieHom.id : L₁ →ₗ⁅R⁆ L₁) = f := rfl

