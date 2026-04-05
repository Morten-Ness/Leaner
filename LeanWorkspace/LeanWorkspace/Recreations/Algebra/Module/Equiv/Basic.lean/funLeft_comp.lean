import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable {m n p : Type*}

theorem funLeft_comp (f₁ : n → p) (f₂ : m → n) :
    LinearMap.funLeft R M (f₁ ∘ f₂) = (LinearMap.funLeft R M f₂).comp (LinearMap.funLeft R M f₁) := rfl

