import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

theorem coe_trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

