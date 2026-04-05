import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem image_symm_eq_preimage (e : R ≃+* S) (s : Set S) : e.symm '' s = e ⁻¹' s := e.toEquiv.image_symm_eq_preimage _

