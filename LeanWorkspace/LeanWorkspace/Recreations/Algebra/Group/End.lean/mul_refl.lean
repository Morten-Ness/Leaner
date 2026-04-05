import Mathlib

variable {A M G α β γ : Type*}

theorem mul_refl (e : Equiv.Perm α) : e * Equiv.refl α = e := Equiv.trans_refl e

