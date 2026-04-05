import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem symm_apply_eq (e : R ≃+* S) {x : S} {y : R} :
    e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

