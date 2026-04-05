import Mathlib

variable {A M G α β γ : Type*}

theorem self_trans_inv (e : Equiv.Perm α) : e.trans e⁻¹ = 1 := Equiv.self_trans_symm e

