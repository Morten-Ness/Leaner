import Mathlib

variable {A M G α β γ : Type*}

theorem mul_def (f g : Equiv.Perm α) : f * g = g.trans f := rfl

