import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem coe_mulEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃* S') = (e₁ : R ≃* S).trans ↑e₂ := rfl

