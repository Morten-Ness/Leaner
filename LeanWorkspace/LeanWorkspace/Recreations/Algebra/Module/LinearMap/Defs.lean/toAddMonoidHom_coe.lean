import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

omit [Module R M₂] in
theorem toAddMonoidHom_coe {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R →+* S}
    (f : M₁ →ₛₗ[σ] M₂) : ⇑f.toAddMonoidHom = f := rfl

