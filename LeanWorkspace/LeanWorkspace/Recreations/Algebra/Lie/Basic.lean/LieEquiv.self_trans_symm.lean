import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]

variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

theorem self_trans_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.trans e.symm = LieEquiv.refl := LieEquiv.ext LieEquiv.symm_apply_apply e

