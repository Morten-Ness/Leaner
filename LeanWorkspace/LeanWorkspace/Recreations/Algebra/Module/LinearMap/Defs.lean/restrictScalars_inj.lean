import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

variable [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]

theorem restrictScalars_inj (fₗ gₗ : M →ₗ[S] M₂) :
    fₗ.restrictScalars R = gₗ.restrictScalars R ↔ fₗ = gₗ := (LinearMap.restrictScalars_injective R).eq_iff

