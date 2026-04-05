import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₁] [Module R M₂] [Module S M₁] [Module S M₂]

variable [SMulCommClass R S M₁] [SMulCommClass R S M₂]

variable [CompatibleSMul M₁ M₂ S R]

theorem compRight_apply (f : M₁ →ₗ[R] M₂) (g : M →ₗ[R] M₁) : LinearMap.compRight S f g = f.comp g := rfl

