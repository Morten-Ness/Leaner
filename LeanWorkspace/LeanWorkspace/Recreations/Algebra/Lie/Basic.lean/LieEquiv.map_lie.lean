import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]

variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

theorem map_lie (e : L₁ ≃ₗ⁅R⁆ L₂) (x y : L₁) : e ⁅x, y⁆ = ⁅e x, e y⁆ := LieHom.map_lie e.toLieHom x y

