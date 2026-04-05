import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x := e.toEquiv.apply_symm_apply

