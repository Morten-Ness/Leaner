import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem coe_toAddEquiv_symm (e : R ≃+* S) : (e.symm : S ≃+ R) = (e : R ≃+ S).symm := rfl

