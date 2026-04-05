import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem toAddEquiv_eq_coe (f : R ≃+* S) : f.toAddEquiv = ↑f := rfl

