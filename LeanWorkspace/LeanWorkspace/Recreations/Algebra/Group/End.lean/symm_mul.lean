import Mathlib

variable {A M G α β γ : Type*}

theorem symm_mul (e : Equiv.Perm α) : e.symm * e = 1 := Equiv.self_trans_symm e

