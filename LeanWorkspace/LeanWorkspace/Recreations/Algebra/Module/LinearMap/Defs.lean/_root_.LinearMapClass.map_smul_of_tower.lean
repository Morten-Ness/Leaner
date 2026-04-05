import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

variable {R S : Type*} [Semiring S] [SMul R M] [Module S M] [SMul R M₂] [Module S M₂]

theorem LinearMap.map_smul_of_tower _root_.LinearMapClass {F : Type*} [CompatibleSMul M M₂ R S]
    [FunLike F M M₂] [LinearMapClass F S M M₂] (fₗ : F) (c : R) (x : M) :
    fₗ (c • x) = c • fₗ x := LinearMap.CompatibleSMul.map_smul (fₗ : M →ₗ[S] M₂) c x

