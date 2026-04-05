import Mathlib

variable {A M G α β γ : Type*}

theorem refl_mul (e : Equiv.Perm α) : Equiv.refl α * e = e := rfl

