import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

theorem isLinearMap_of_compatibleSMul [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]
    (f : M →ₗ[S] M₂) : IsLinearMap R f where
  LinearMap.map_add := LinearMap.map_add f
  LinearMap.map_smul := LinearMap.map_smul_of_tower f

