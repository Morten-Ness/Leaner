import Mathlib

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} (M : Type w₁)

variable [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [LieRingModule L₂ M]

variable (f : L₁ →ₗ⁅R⁆ L₂)

theorem LieModule.compLieHom [Module R M] [LieModule R L₂ M] :
    @LieModule R L₁ M _ _ _ _ _ (LieRingModule.compLieHom M f) := { __ := LieRingModule.compLieHom M f
    smul_lie := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, smul_lie, map_smul]
    lie_smul := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, lie_smul] }

