import Mathlib

variable {F α β R S S' : Type*}

variable [Add R] [Add S] [Mul R] [Mul S]

theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R := RingEquiv.ext e.left_inv

