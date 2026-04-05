import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f := rfl

