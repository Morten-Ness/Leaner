import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem toMulEquiv_eq_coe (f : R ≃+* S) : f.toMulEquiv = ↑f := rfl

