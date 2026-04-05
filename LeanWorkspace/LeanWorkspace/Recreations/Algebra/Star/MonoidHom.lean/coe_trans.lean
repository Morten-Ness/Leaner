import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem coe_trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

