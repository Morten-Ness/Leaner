import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem symm_trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

