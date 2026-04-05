import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem eq_symm_apply (e : R ≃+* S) {x : S} {y : R} :
    y = e.symm x ↔ e y = x := Equiv.eq_symm_apply _

