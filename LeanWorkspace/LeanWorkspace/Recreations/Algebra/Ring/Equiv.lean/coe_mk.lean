import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem coe_mk (e h₃ h₄) : ⇑(⟨e, h₃, h₄⟩ : R ≃+* S) = e := rfl

