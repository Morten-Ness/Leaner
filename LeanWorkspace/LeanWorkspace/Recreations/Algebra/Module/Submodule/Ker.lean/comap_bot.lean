import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p : Submodule R M)

variable {τ₁₂ : R →+* R₂}

theorem comap_bot (f : M →ₛₗ[τ₁₂] M₂) : comap f ⊥ = LinearMap.ker f := rfl

