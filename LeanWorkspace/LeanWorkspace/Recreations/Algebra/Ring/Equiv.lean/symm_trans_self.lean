import Mathlib

variable {F α β R S S' : Type*}

variable [Add R] [Add S] [Mul R] [Mul S]

theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S := RingEquiv.ext e.right_inv

