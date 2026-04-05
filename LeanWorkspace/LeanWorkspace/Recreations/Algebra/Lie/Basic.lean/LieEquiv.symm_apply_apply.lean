import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]

variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

theorem symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e.symm (e x) = x := e.toLinearEquiv.symm_apply_apply

