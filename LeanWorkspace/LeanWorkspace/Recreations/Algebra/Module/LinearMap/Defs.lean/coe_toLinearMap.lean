import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Semiring R] [Module R M] [Semiring S] [Module S M₂] [Module R M₃]

variable {σ : R →+* S}

theorem coe_toLinearMap (f : M →ₑ+[σ.toMonoidHom] M₂) : ((f : M →ₛₗ[σ] M₂) : M → M₂) = f := rfl

