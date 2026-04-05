import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x := e.toEquiv.symm_apply_apply

