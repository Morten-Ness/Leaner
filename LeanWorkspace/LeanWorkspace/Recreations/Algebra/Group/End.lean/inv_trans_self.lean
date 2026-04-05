import Mathlib

variable {A M G α β γ : Type*}

theorem inv_trans_self (e : Equiv.Perm α) : e⁻¹.trans e = 1 := Equiv.symm_trans_self e

