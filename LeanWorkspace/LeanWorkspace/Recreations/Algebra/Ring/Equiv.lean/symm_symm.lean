import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem symm_symm (e : R ≃+* S) : e.symm.symm = e := rfl

