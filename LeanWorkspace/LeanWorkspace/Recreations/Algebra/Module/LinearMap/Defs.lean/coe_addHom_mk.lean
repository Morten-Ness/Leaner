import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable {σ : R →+* S}

theorem coe_addHom_mk {σ : R →+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M →ₛₗ[σ] M₃) : AddHom M M₃) = f := rfl

