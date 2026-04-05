import Mathlib

variable {M : Type*}

variable [MulOneClass M]

theorem sup_def {s₁ s₂ : SaturatedSubmonoid M} :
    s₁ ⊔ s₂ = (s₁.toSubmonoid ⊔ s₂.toSubmonoid).saturation := rfl

