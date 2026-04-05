import Mathlib

variable {A M G α β γ : Type*}

theorem mul_apply (f g : Equiv.Perm α) (x) : (f * g) x = f (g x) := rfl

