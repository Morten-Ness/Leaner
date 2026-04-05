import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem symm_trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

