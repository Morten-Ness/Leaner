import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem LieEquiv.isEngelian_iff (e : L ≃ₗ⁅R⁆ L₂) :
    LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L ↔ LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ := ⟨e.surjective.isEngelian, e.symm.surjective.isEngelian⟩

