import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable (f : M →ₗ[R] M₂)

theorem smulRightₗ_apply_apply (f : M₂ →ₗ[R] R) (x : M) (y : M₂) :
    LinearMap.smulRightₗ f x y = f y • x := rfl

