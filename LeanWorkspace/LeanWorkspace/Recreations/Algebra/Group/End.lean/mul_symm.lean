import Mathlib

variable {A M G α β γ : Type*}

theorem mul_symm (e : Equiv.Perm α) : e * e.symm = 1 := Equiv.symm_trans_self e

