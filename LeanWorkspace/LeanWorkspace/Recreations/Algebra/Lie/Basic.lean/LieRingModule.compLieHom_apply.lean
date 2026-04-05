import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} (M : Type w₁)

variable [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [LieRingModule L₂ M]

variable (f : L₁ →ₗ⁅R⁆ L₂)

theorem LieRingModule.compLieHom_apply (x : L₁) (m : M) :
    haveI := LieRingModule.compLieHom M f
    ⁅x, m⁆ = ⁅f x, m⁆ :=
  rfl

