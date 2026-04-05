import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem image_eq_preimage_symm (e : R ≃+* S) (s : Set R) : e '' s = e.symm ⁻¹' s := e.toEquiv.image_eq_preimage_symm _

