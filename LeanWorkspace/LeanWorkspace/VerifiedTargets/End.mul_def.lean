import Mathlib

variable {G M N A α : Type*}

theorem mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl

--TODO - This statement should be something like `toFun 1 = id`

