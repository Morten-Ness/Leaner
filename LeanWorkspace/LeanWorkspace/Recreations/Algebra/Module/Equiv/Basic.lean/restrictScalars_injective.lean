import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring S] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂] [Module S M] [Module S M₂]
  [LinearMap.CompatibleSMul M M₂ R S]

theorem restrictScalars_injective :
    Function.Injective (LinearEquiv.restrictScalars R : (M ≃ₗ[S] M₂) → M ≃ₗ[R] M₂) := fun _ _ h ↦
  ext (LinearEquiv.congr_fun h :)

