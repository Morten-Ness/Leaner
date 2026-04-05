import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm := rfl

