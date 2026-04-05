import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem symm_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := rfl

