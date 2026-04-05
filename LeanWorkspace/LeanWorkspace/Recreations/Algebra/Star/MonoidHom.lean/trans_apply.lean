import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) := rfl

