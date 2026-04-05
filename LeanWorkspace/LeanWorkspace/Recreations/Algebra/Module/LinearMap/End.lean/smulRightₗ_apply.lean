import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable (f : M →ₗ[R] M₂)

theorem smulRightₗ_apply (f : M₂ →ₗ[R] R) (x : M) :
    (LinearMap.smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M) f x = LinearMap.smulRight f x := rfl

